# Contributing

Report errors in a theorem statement, the paper-to-Lean correspondence, a
proof, or the reproduction instructions through
[GitHub issues](https://github.com/dcond/TraceableAgency/issues). Include the
paper result or Lean declaration concerned. For a build failure, include the
commit, operating system, command, and relevant error output.

## Making a change

Use the toolchain and dependency revisions already pinned in the repository.
Keep proof changes separate from dependency upgrades. Preserve existing public
declarations and archived paper versions unless a change to them is explicitly
part of the contribution. Explain any changed statement or hypothesis in the
pull request and update its correspondence entry in `Certificate/`.

Build the public library after changing Lean code:

```bash
lake exe cache get
lake build TraceableAgency
```

When adding a Lean module, include it in the appropriate public import and in
`TraceableAgency/Audit/TrustBoundaryImports.lean`. Check the audit inventory:

```bash
python3 scripts/check_trust_imports.py
```

Do not edit `.lake/` or commit generated Lean build products. The full audit
rebuilds project sources and rejects proof holes, new project axioms, and
unchecked proof mechanisms.

## Paper and generated files

The current paper is `Paper/trace_tempered_choice_v11.tex`. After a source
change, use TeX Live 2026 and `latexmk` to regenerate and check its PDF:

```bash
./scripts/build_paper.sh --update v11
./scripts/build_paper.sh --check v11
```

If a change affects the generated Theorem 1 specification, regenerate it with
`./scripts/build_theorem1_spec.sh --update` and review the diff. Keep the
claim maps aligned with the statements actually proved.

After all intended edits, refresh the repository's byte manifest and run the
complete audit from a clean dependency checkout:

```bash
./scripts/update_certificate_manifest.sh --update
./scripts/update_certificate_manifest.sh --check
./scripts/check_trust_boundary.sh
git diff --check
```

The manifest includes tracked files and non-ignored new files, so keep scratch
work outside the repository or in its ignored `tmp/` directory. Include the
updated manifest in the same commit as the changes it records.

Describe the mathematical or documentation change and the checks run in the
pull request. The current proof conventions and verification scope are in the
[formalization certificate](Certificate/FORMALIZATION_CERTIFICATE.md) and
[trust report](Certificate/TRUST_BOUNDARY.md). Existing software and paper
licences continue to apply; retain the attribution and licence for vendored
code.
