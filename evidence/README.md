# Verification evidence

`historical/` is the actual 2026-10-27 combined run: 407 existing theorems and five independent interface checks, 626 named declarations, 37 freshly built project modules. These are historical results, not a claim that GitHub Actions has already run.

Only host-specific path prefixes were replaced during export. `${HISTORICAL_RUN}` identifies the original run root; `${ORIGINAL_PROJECT}`, `${PRIOR_REVISION3_RUN}` and `${HOME}` are provenance placeholders, not runtime dependencies. `export_manifest.json` records both original-byte and exported-byte SHA-256 hashes. Logs without host paths remain byte-identical.

The package's fresh local reproduction is separately recorded in `portable-test/` after it completes. GitHub-hosted execution and a cold dependency download are recorded separately in `PACKAGE_STATUS.json`; unexecuted work is NOT_RUN.

The raw source packages and original evidence are not overwritten. The bundled LaTeX snapshot retains its original hash; it describes the manuscript baseline, not a replacement for the current verification status.
