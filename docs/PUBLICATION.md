# Publication provenance

This repository publishes the independently validated PDEL verification package with English documentation. The publication copy preserves all 78 locked source, configuration, and verification-tool files, all 37 project Lean modules, and the previous compiler/axiom/type/dependency evidence byte-for-byte.

## Stable manuscript correspondence

The current paper snapshot changes only repository/release links and verification-status prose. It reports the actual recorded local builds and retains the coverage limitations. An automated comparison confirmed that mathematical blocks, theorem/proof blocks, inline mathematics, and stable LaTeX label lists are unchanged across the six edited manuscript sources. No Lean theorem, assumption, or proof was edited for publication.

The baseline manuscript and mapping remain in `paper/baseline/` and `docs/baseline/`. The current mapping has been rebound to the publication manuscript hash; its declaration associations, assumptions, and uncovered-content entries remain unchanged. Both hashes are recorded in the current mapping. Historical relative paths in the baseline map identify the original baseline snapshot.

## Manuscript build evidence

The linked manuscript was compiled separately with its existing figures and bibliography. Both the 33-page full article and 8-page supplement compiled successfully. The build logs are exported under `evidence/publication/`; local path prefixes are replaced with descriptive placeholders. Repository and release link targets were checked in the generated PDFs. The PDFs and complete manuscript assets are retained with the author's publication records rather than bundled in this Lean repository.

These successful builds do not establish a standalone LaTeX build from this repository: the repository intentionally contains semantic snapshots, without the full figure and numerical-analysis supplement. That standalone build remains **NOT_RUN**.

## Status interpretation

`PACKAGE_STATUS.json` is the preserved snapshot of the earlier relocated local verification. In particular, its cloud-CI, cold-download, and LaTeX fields describe that earlier package test; they are not live deployment status. Publication manuscript-build evidence is recorded separately. Current GitHub CI results are available at <https://github.com/hl-ren/pdel-lean-verification/actions/workflows/verify.yml>.

Repository: <https://github.com/hl-ren/pdel-lean-verification>

Versioned verification release: <https://github.com/hl-ren/pdel-lean-verification/releases/tag/v1.0.0>
