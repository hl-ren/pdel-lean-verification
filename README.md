# PDEL: Lean formalization

Lean 4 formalization accompanying *A path-dependent entropic Lagrangian formulation for exact thermoviscous evolution of sheared magnetic tori with anisotropic resistivity*.

[Paper: arXiv:2610.37305v1](https://arxiv.org/abs/2610.37305v1) · [Verification archive v1.0.2](https://github.com/hl-ren/pdel-lean-verification/releases/tag/v1.0.2) · [Declaration correspondence](docs/REVISION3_STATEMENT_MAP.json)

## Mathematical scope

| Library | Scope | Theorems | Named declarations |
|---|---|---:|---:|
| `PdelMHD` | Finite-dimensional passivity and balance identities | 37 | 44 |
| `PdelBasic` | Single-degree-of-freedom thermoviscoelasticity | 66 | 100 |
| `PdelEulerian` | Single-temperature, magnetic-quasistatic Eulerian MHD; fixed-box integration | 217 | 354 |
| `PdelBridge` | Conditional correspondences among the three layers | 41 | 59 |
| `PdelRevision3` | Nonmagnetic specialization and scalar history/budget identities | 46 | 64 |
| `PdelIntegration` | Cross-library compatibility checks | 5 | 5 |

The formalization contains 407 mathematical theorems and five interface checks. Its 37 modules comprise 626 named declarations. Cross-layer statements retain their normalization, reference-state and interface-power hypotheses. The Revision3 history results concern the prescribed scalar expansion branch.

Full Maxwell dynamics, the two-temperature PDE system, toroidal embedding, moving-boundary energy balance, a complete three-dimensional homologous field/flow realization, stability and physical validation lie outside the formalized scope. These items are marked `NOT_RUN` in the verification records.

## Reproduction

The development uses **Lean 4.19.0** and mathlib commit `c44e0c8ee63ca166450922a373c7409c5d26b00b`. All nine third-party dependency revisions are fixed in [the dependency manifest](verification/dependencies.lock.json).

Requirements: Python 3.11 or later, Git and curl; macOS also requires Apple Command Line Tools.

```sh
git clone --branch v1.0.2 https://github.com/hl-ren/pdel-lean-verification.git
cd pdel-lean-verification
bash verify.sh
```

The script installs the pinned Lean toolchain if necessary, obtains the dependency sources and mathlib cache, and compiles the project in a new directory under `verification-runs/`. Each run starts without project build products. Its `report/` directory contains compiler output, complete declaration types, axiom dependencies, import and proof-dependency checks, and source hashes.

An existing cache of the nine pinned third-party packages can be supplied with `--dependency-cache /absolute/path/to/packages`. Dependency commits and tracked files are checked before use. Project build products are excluded from cache reuse.

`bash verify.sh --check-only` validates source and configuration integrity without executing Lean; compilation and axiom auditing are reported as `NOT_RUN` for that mode.

## Verification records

The [Ubuntu verification run](https://github.com/hl-ren/pdel-lean-verification/actions/runs/40515165759) completed a fresh dependency fetch, compilation, axiom audit, type extraction and dependency analysis. The full report is archived with [v1.0.2](https://github.com/hl-ren/pdel-lean-verification/releases/tag/v1.0.2). The logical dependencies are limited to `Classical.choice`, `Quot.sound` and `propext`.

The repository retains the Lean sources, audit drivers, declaration registries, dependency locks, CI workflow and manuscript correspondence needed to reproduce these checks. Historical logs and complete types remain in the versioned verification archive; a new run writes fresh evidence locally.

The [declaration registry](verification/declarations.json), [source lock](verification/source_lock.json) and [proof-source hashes](verification/proof_source_provenance.json) identify the audited sources. The [manuscript correspondence](docs/REVISION3_STATEMENT_MAP.json) uses stable LaTeX labels and records declarations, hypotheses and coverage limits. Manuscript sources and figures are distributed separately.

## Checksums

`SHA256SUMS` lists the hashes of the repository files. To verify an extracted archive:

```sh
shasum -a 256 -c SHA256SUMS
```

Each release ZIP has a separate SHA-256 checksum file.
