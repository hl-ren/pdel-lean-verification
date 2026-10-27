# Verification record

## Versions and environment

The proof archive is [v1.0.1](https://github.com/hl-ren/pdel-lean-verification/releases/tag/v1.0.1), commit `66181d74011906d2ba5aab18693d750e4a2fdb21`. It uses Lean 4.19.0 and mathlib commit `c44e0c8ee63ca166450922a373c7409c5d26b00b`. Subsequent manuscript and documentation edits retain the proof sources and dependency revisions recorded in that archive.

The [Ubuntu run](https://github.com/hl-ren/pdel-lean-verification/actions/runs/40495422483) compiled all 37 modules from source and audited 626 declarations. Compilation, axiom auditing, complete-type extraction and dependency checks succeeded. The release includes the compiler and audit reports, workflow log and checksums. Local runs are indexed in [the evidence directory](../evidence/README.md).

The audit admits only `Classical.choice`, `Quot.sound` and `propext`. The source gate rejects incomplete proofs and custom result axioms. The [declaration registry](../verification/declarations.json) and [source lock](../verification/source_lock.json) identify the audited targets and file hashes.

## Manuscript correspondence

The [correspondence table](REVISION3_STATEMENT_MAP.json) associates stable manuscript labels with Lean declarations, hypotheses and coverage limits. Its manuscript hash identifies the current source. The [baseline manuscript](../paper/baseline/PDEL_Toroidal_Journal_Full.tex) and [baseline mapping](baseline/REVISION3_STATEMENT_MAP.json) identify the earlier audited text.

The Lean development covers a finite-dimensional core, a single-degree-of-freedom thermoviscoelastic specialization, single-temperature magnetic-quasistatic Eulerian MHD on a fixed box, conditional inter-layer results and the specified scalar history identities. It does not formalize the full Maxwell system, two-temperature PDEs, toroidal embedding, moving boundaries, a complete three-dimensional homologous solution, stability or physical validation.

## Reading the records

Each report describes the run that produced it. `NOT_RUN` denotes an operation outside that run or its scope. In particular, `PACKAGE_STATUS.json` records the local package test preceding the Ubuntu run; its cloud-execution fields are historical. The repository's LaTeX snapshots do not include the complete figure and numerical-analysis supplement, and a standalone manuscript build from these files is `NOT_RUN`.

Host-specific prefixes in exported local logs are represented by documented placeholders. Original and exported hashes are listed in [the export manifest](../evidence/export_manifest.json).

## Dependency setup

Version 1.0.1 fetches the ProofWidgets release tag required by Lake and verifies that it resolves to the pinned commit. Version 1.0.0 omitted this tag during a shallow fetch. The [initial cloud-run report](../evidence/first-github-run/README.md) records that setup failure; project compilation and auditing had not started. The correction leaves dependency revisions and Lean sources unchanged.

Repository and release access is currently restricted.
