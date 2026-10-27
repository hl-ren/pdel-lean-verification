# Dependency setup: v1.0.0

[Run 40495033001](https://github.com/hl-ren/pdel-lean-verification/actions/runs/40495033001), commit `479cb9c5ab9e99bfea19ba69f8fc0787f0a127f5`.

The shallow dependency fetch omitted the ProofWidgets release tag required by Lake to locate its cache archive. Compilation, axiom auditing, type extraction and proof-dependency analysis were consequently `NOT_RUN`.

Version 1.0.1 fetches that tag and checks it against the same pinned commit. Its [complete Ubuntu verification](https://github.com/hl-ren/pdel-lean-verification/actions/runs/40495422483) succeeded. The files in this directory retain the initial run's diagnostics.
