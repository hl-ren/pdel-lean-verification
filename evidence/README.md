# Verification records

| Record | Contents |
|---|---|
| [Combined local run](historical/summary.json) | Compilation and audit of the three layers, bridges, Revision3 modules and interface checks. |
| [Independent package build](portable-test/summary.json) | Reproduction from an isolated copy with pinned third-party dependencies. |
| [Ubuntu run](https://github.com/hl-ren/pdel-lean-verification/actions/runs/40495422483) | Fresh dependency fetch and complete compilation, axiom, type and dependency checks; reports archived in [v1.0.1](https://github.com/hl-ren/pdel-lean-verification/releases/tag/v1.0.1). |
| [Initial cloud run](first-github-run/README.md) | Dependency-cache setup failure in v1.0.0. |
| `publication/` | LaTeX build records and manuscript correspondence checks from the initial repository publication. |

The successful proof runs cover 407 mathematical theorems, five interface checks and 626 named declarations in 37 modules. The [declaration audit](historical/declaration_status.json), [axiom output](historical/06_all_axioms.log) and [complete types](historical/07_all_full_types.log) give the individual results.

Exported local logs replace host-specific prefixes only. `${HISTORICAL_RUN}`, `${ORIGINAL_PROJECT}`, `${PRIOR_REVISION3_RUN}` and `${HOME}` identify the original locations. [The export manifest](export_manifest.json) records original and exported SHA-256 hashes.

Status fields apply to the associated run. `NOT_RUN` marks checks that were not executed in that run; later results are recorded separately. Mathematical coverage limits are specified in the manuscript correspondence and repository documentation.
