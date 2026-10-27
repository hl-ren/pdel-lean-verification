# PDEL Lean verification

Reproducible Lean 4 compilation, per-declaration axiom audits, and cross-layer dependency checks for **PDEL Toroidal Journal, Revision 3**.

[Verification release v1.0.0](https://github.com/hl-ren/pdel-lean-verification/releases/tag/v1.0.0) · [GitHub Actions](https://github.com/hl-ren/pdel-lean-verification/actions/workflows/verify.yml)

## Recorded verification

| Project | Theorems | Named declarations audited |
|---|---:|---:|
| PdelMHD / Layer 1 | 37 | 44 |
| PdelBasic / Layer 2 | 66 | 100 |
| PdelEulerian / Layer 3 | 217 | 354 |
| PdelBridge | 41 | 59 |
| PdelRevision3 | 46 | 64 |
| Independent PdelIntegration checks | 5 | 5 |

The existing projects contain **407 theorems**; the **5 independent interface checks** are counted separately. The recorded local runs freshly compiled **37 project modules** and audited **626 named declarations**. Compilation, full-type extraction, axiom auditing, and dependency checks all passed. The allowed axiom set is `Classical.choice`, `Quot.sound`, and `propext`; `sorryAx` and custom result axioms are rejected.

All 37 Lean source modules retain their original bytes, theorem statements, hypotheses, and proofs. See [proof-source provenance](verification/proof_source_provenance.json). Lean is pinned to **4.19.0**, and mathlib to commit `c44e0c8ee63ca166450922a373c7409c5d26b00b`.

## Reproduce the checks

Requirements: Python 3.11+, Git, and curl. On macOS, install Apple Command Line Tools. The verification entry point supports macOS and Linux.

```sh
git clone https://github.com/hl-ren/pdel-lean-verification.git
cd pdel-lean-verification
bash verify.sh
```

The first run installs Elan if needed, obtains the pinned Lean toolchain and all nine third-party dependencies at the exact commits in [the dependency lock](verification/dependencies.lock.json), and downloads the mathlib cache. Network access and sufficient disk space are required.

Each run creates a new `verification-runs/run-*/` directory. It copies the source into an independent `kit/` and builds each project's `.lake/build` from an empty directory. Only pinned third-party dependency artifacts may be reused; the project's own previous build products are never copied. The run's `report/` contains actual logs, exit codes, declaration statuses, axiom dependencies, full types, module-resolution paths, and source hashes.

Optionally, reuse an existing directory containing the nine pinned third-party Git packages:

```sh
bash verify.sh --dependency-cache /absolute/path/to/packages
```

This option validates dependency commits and tracked working-tree state. It does not accept project build products as a cache.

For package integrity, source-policy, declaration-registry, and configuration checks only:

```sh
bash verify.sh --check-only
```

This command reports compilation and axiom auditing as **NOT_RUN**. It is not a Lean proof check. Modified sources, registries, or pinned configurations are rejected by the entry point rather than silently matched to old results.

## Continuous integration and evidence

The [GitHub Actions workflow](.github/workflows/verify.yml) runs on pushes, pull requests, and manual dispatch. It performs a fresh verification and uploads the actual reports. Action versions are pinned to commits. Project build artifacts are not cached.

The bundled local evidence predates GitHub publication. Its GitHub Actions and cold dependency-download fields therefore remain **NOT_RUN**. Current cloud execution status is shown on the [Actions page](https://github.com/hl-ren/pdel-lean-verification/actions/workflows/verify.yml); a repository upload or a green package-integrity check alone does not establish a successful cloud Lean run.

- [Local package status](PACKAGE_STATUS.json) and [successful relocated package run](evidence/portable-test/summary.json).
- [Historical evidence guide](evidence/README.md) and [combined-run summary](evidence/historical/summary.json).
- [Per-declaration statuses](evidence/historical/declaration_status.json), [actual axiom output](evidence/historical/06_all_axioms.log), and [complete declaration types](evidence/historical/07_all_full_types.log).
- [Stable LaTeX label / Lean declaration / hypotheses / uncovered-content mapping](docs/REVISION3_STATEMENT_MAP.json).
- [Source and tool lock](verification/source_lock.json), [declaration registry](verification/declarations.json), and [dependency lock](verification/dependencies.lock.json).

Historical log exports replace local path prefixes only. Declaration names, types, axioms, statuses, and mathematical content are preserved. Original/export SHA-256 pairs are recorded in [the export manifest](evidence/export_manifest.json). The original verification results remain preserved outside this publication copy.

## Manuscript provenance

The [Revision3 LaTeX snapshot](paper/PDEL_Toroidal_Journal_Full.tex) includes the public repository and versioned release links, with verification-status prose updated to reflect the recorded local runs. Mathematical statements, mathematical assumptions, equations, and stable labels are unchanged.

The [original audited manuscript](paper/baseline/PDEL_Toroidal_Journal_Full.tex) and [original statement mapping](docs/baseline/REVISION3_STATEMENT_MAP.json) remain available byte-for-byte. The current mapping records both manuscript hashes. The baseline mapping's historical paper path refers to that original snapshot. See [publication provenance](docs/PUBLICATION.md).

The repository contains LaTeX snapshots for semantic traceability. It does not include the manuscript's complete figure and numerical-analysis supplement, so a standalone manuscript build from this repository is **NOT_RUN**.

## Coverage boundaries

- **Layer 1:** finite-dimensional and algebraic core.
- **Layer 2:** a single-degree-of-freedom thermoviscoelastic specialization.
- **Layer 3:** single-temperature, magnetic-quasistatic Eulerian MHD and fixed-box proofs.
- **Cross-layer bridges:** conditional correspondences retaining their normalization, reference-state, and interface-port hypotheses.
- **Revision3:** scalar calculations on the prescribed branch, including the nonmagnetic specialization, the four-to-one cumulative pressure-work / irreversible-heat relation, and current-volume Joule-history derivatives, extrema, and monotonic intervals.

Revision3 directly imports Layers 2 and 3. Five independent interface checks also connect its power coefficient to Layer 1, its three cumulative quantities to Layer 2's integral definition, and its nonmagnetic reference state to the existing bridge. These results do not establish unconditional equivalence of complete models.

**NOT_RUN / outside the certified scope:** full Maxwell theory, the two-temperature PDE system, toroidal embedding, moving boundaries, a complete three-dimensional homologous-expansion field/material-map realization, stability, and physical validation.

## File integrity

`SHA256SUMS` covers every distributed repository file except itself. After extracting the release archive, run:

```sh
shasum -a 256 -c SHA256SUMS
```

The release also includes a separate SHA-256 file for the ZIP archive. Generated run directories are excluded from the distributed package.
