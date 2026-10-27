# Publication provenance

This repository publishes the independently validated PDEL verification package with English documentation. The initial v1.0.0 publication preserved all 78 locked source, configuration, and verification-tool files. All 37 project Lean modules and the previous local compiler/axiom/type/dependency evidence remain byte-for-byte unchanged in v1.0.1. The v1.0.1 correction changes only dependency-fetch tooling and its recorded hash, as described below.

## Stable manuscript correspondence

The current paper snapshot changes only repository/release links and verification-status prose. It reports the actual recorded local builds and retains the coverage limitations. An automated comparison confirmed that mathematical blocks, theorem/proof blocks, inline mathematics, and stable LaTeX label lists are unchanged across the six edited manuscript sources. No Lean theorem, assumption, or proof was edited for publication.

The baseline manuscript and mapping remain in `paper/baseline/` and `docs/baseline/`. The current mapping has been rebound to the publication manuscript hash; its declaration associations, assumptions, and uncovered-content entries remain unchanged. Both hashes are recorded in the current mapping. Historical relative paths in the baseline map identify the original baseline snapshot.

## Manuscript build evidence

The linked manuscript was compiled separately with its existing figures and bibliography. Both the 33-page full article and 8-page supplement compiled successfully. The build logs are exported under `evidence/publication/`; local path prefixes are replaced with descriptive placeholders. Repository and release link targets were checked in the generated PDFs. The PDFs and complete manuscript assets are retained with the author's publication records rather than bundled in this Lean repository.

These successful builds do not establish a standalone LaTeX build from this repository: the repository intentionally contains semantic snapshots, without the full figure and numerical-analysis supplement. That standalone build remains **NOT_RUN**.

## Status interpretation

`PACKAGE_STATUS.json` is the preserved snapshot of the earlier relocated local verification. In particular, its cloud-CI, cold-download, and LaTeX fields describe that earlier package test; they are not live deployment status. Publication manuscript-build evidence is recorded separately. Current GitHub CI results are available at <https://github.com/hl-ren/pdel-lean-verification/actions/workflows/verify.yml>.

Repository: <https://github.com/hl-ren/pdel-lean-verification>

Versioned verification release: <https://github.com/hl-ren/pdel-lean-verification/releases/tag/v1.0.1>

## v1.0.1 dependency-fetch correction

The [first GitHub run](https://github.com/hl-ren/pdel-lean-verification/actions/runs/40495033001) failed before any project Lean build or axiom audit. Exact-commit shallow fetches omitted the ProofWidgets release tag; Lake 4.19 resolves this dependency's archive using an exact tag at HEAD. The failed run's status and cache log are preserved under `evidence/first-github-run/`.

The verifier now fetches the locked ProofWidgets input tag and checks that the tag resolves to the already pinned commit. It does not change dependency versions, proof sources, declaration targets, allowed axioms, or mathematical assumptions. This also avoids silently trusting a tag if it has been moved. The original v1.0.0 release remains available as a historical publication; v1.0.1 supersedes it for reproduction.
