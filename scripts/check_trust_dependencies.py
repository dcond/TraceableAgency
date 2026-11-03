#!/usr/bin/env python3
"""Offline source-pin checks for the installed Lean dependency checkout.

This does not download packages or authenticate generated .olean/native files.
Tracked files are hashed against HEAD directly, independently of Git's index
stat cache, assume-unchanged flags, and skip-worktree flags.
"""
from __future__ import annotations

import hashlib
import json
import os
from pathlib import Path
import re
import stat
import subprocess
import sys


class CheckFailure(RuntimeError):
    pass


def run(*args: str, cwd: Path) -> bytes:
    result = subprocess.run(args, cwd=cwd, stdout=subprocess.PIPE,
                            stderr=subprocess.PIPE, check=False)
    if result.returncode:
        raise CheckFailure(f"{' '.join(args)} failed: "
                           f"{result.stderr.decode(errors='replace').strip()}")
    return result.stdout


def object_hash(kind: str, content: bytes, algorithm: str) -> str:
    header = f"{kind} {len(content)}\0".encode()
    return hashlib.new(algorithm, header + content).hexdigest()


def check_package(repo: Path, package: dict) -> int:
    expected = package["rev"]
    actual = run("git", "rev-parse", "--verify", "HEAD", cwd=repo).decode().strip()
    if actual != expected:
        raise CheckFailure(f"{package['name']}: HEAD {actual} differs from pin {expected}")
    algorithm = run("git", "rev-parse", "--show-object-format", cwd=repo).decode().strip()
    if algorithm not in {"sha1", "sha256"}:
        raise CheckFailure(f"{package['name']}: unsupported Git object format {algorithm}")
    commit = run("git", "cat-file", "commit", expected, cwd=repo)
    if object_hash("commit", commit, algorithm) != expected:
        raise CheckFailure(f"{package['name']}: pinned commit object has invalid bytes")
    status = run("git", "status", "--porcelain=v1", "--untracked-files=all", cwd=repo)
    if status:
        raise CheckFailure(f"{package['name']}: checkout is not clean:\n"
                           + status.decode(errors="replace"))
    # Verify tree bytes as well as each tracked blob. An intact commit hash must
    # identify the tree actually used for the comparison below.
    root_tree = commit.splitlines()[0].removeprefix(b"tree ").decode()
    todo = [root_tree]
    seen = set()
    hash_bytes = hashlib.new(algorithm).digest_size
    while todo:
        tree_id = todo.pop()
        if tree_id in seen:
            continue
        seen.add(tree_id)
        tree = run("git", "cat-file", "tree", tree_id, cwd=repo)
        if object_hash("tree", tree, algorithm) != tree_id:
            raise CheckFailure(f"{package['name']}: invalid tree object {tree_id}")
        offset = 0
        while offset < len(tree):
            end = tree.index(b"\0", offset)
            mode = tree[offset:end].split(b" ", 1)[0]
            object_id = tree[end + 1:end + 1 + hash_bytes].hex()
            if mode == b"40000":
                todo.append(object_id)
            offset = end + 1 + hash_bytes
    count = 0
    entries = run("git", "ls-tree", "-r", "-z", expected, cwd=repo)
    for entry in entries.split(b"\0"):
        if not entry:
            continue
        metadata, raw_path = entry.split(b"\t", 1)
        mode, kind, expected_blob = metadata.decode().split()
        path = repo / os.fsdecode(raw_path)
        if kind == "commit" and mode == "160000":
            # A historical, unpopulated gitlink can remain in a pinned tree
            # without supplying any imported source (aesop has one for Std).
            if (not path.exists() and not path.is_symlink()) or (
                    path.is_dir() and not path.is_symlink() and not any(path.iterdir())):
                print(f"EMPTY_GITLINK {package['name']} path={os.fsdecode(raw_path)} "
                      f"revision={expected_blob}")
            else:
                count += check_package(path, {"name": f"{package['name']}/{os.fsdecode(raw_path)}",
                                              "rev": expected_blob})
            continue
        if kind != "blob" or mode not in {"100644", "100755", "120000"}:
            raise CheckFailure(f"{package['name']}: unsupported tracked entry {path}: {mode} {kind}")
        try:
            file_mode = path.lstat().st_mode
            if mode == "120000":
                if not stat.S_ISLNK(file_mode):
                    raise CheckFailure(f"tracked symlink replaced: {path}")
                content = os.fsencode(os.readlink(path))
            else:
                if not stat.S_ISREG(file_mode):
                    raise CheckFailure(f"tracked file replaced: {path}")
                if bool(file_mode & 0o111) != (mode == "100755"):
                    raise CheckFailure(f"tracked executable mode differs: {path}")
                content = path.read_bytes()
        except OSError as error:
            raise CheckFailure(f"cannot read tracked file {path}: {error}") from error
        if object_hash("blob", content, algorithm) != expected_blob:
            raise CheckFailure(f"tracked bytes differ from the pinned commit: {path}")
        count += 1
    return count


def main() -> None:
    root = Path(__file__).resolve().parent.parent
    manifest = json.loads((root / "lake-manifest.json").read_text())
    packages = manifest["packages"]
    names = [package["name"] for package in packages]
    if len(names) != len(set(names)) or not names:
        raise CheckFailure("dependency manifest has duplicate or empty package inventory")
    package_dir = root / manifest["packagesDir"]
    installed = {path.name for path in package_dir.iterdir() if path.is_dir()}
    if installed != set(names):
        raise CheckFailure(f"package inventory mismatch: missing={sorted(set(names)-installed)}, "
                           f"extra={sorted(installed-set(names))}")
    for package in packages:
        if package.get("type") != "git" or package.get("subDir") is not None:
            raise CheckFailure(f"unsupported unpinned/subdirectory dependency: {package['name']}")
        count = check_package(package_dir / package["name"], package)
        print(f"DEPENDENCY_OK {package['name']} revision={package['rev']} tracked_files={count}")
    pin = (root / "lean-toolchain").read_text().strip()
    match = re.fullmatch(r"leanprover/lean4:v(\d+\.\d+\.\d+(?:-[A-Za-z0-9.]+)?)", pin)
    if match is None:
        raise CheckFailure(f"expected an exact Lean release pin, found {pin!r}")
    # `elan which` resolves an already-installed toolchain without invoking its
    # auto-installing Lean shim. Then run the resolved binary directly.
    lean = Path(run("elan", "which", "lean", cwd=root).decode().strip())
    version = run(str(lean), "--version", cwd=root).decode().strip()
    actual_version = re.search(r"\bversion ([^,\s)]+)", version)
    if actual_version is None or actual_version.group(1) != match.group(1):
        raise CheckFailure(f"Lean version differs from {pin}: {version}")
    print(f"LEAN_PIN_OK pin={pin} executable={lean}")
    print(version)
    print(f"Dependency trust check passed: {len(packages)} pinned source checkouts.")
    print("Boundary: ignored build/cache artifacts and release-binary provenance are not authenticated.")


if __name__ == "__main__":
    try:
        main()
    except (CheckFailure, OSError, ValueError, KeyError) as error:
        print(f"ERROR: {error}", file=sys.stderr)
        sys.exit(1)
