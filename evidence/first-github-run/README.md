# First cloud run: preserved failure

Run: <https://github.com/hl-ren/pdel-lean-verification/actions/runs/40495033001>

Commit: `479cb9c5ab9e99bfea19ba69f8fc0787f0a127f5` (v1.0.0).

The dependency fetch succeeded, but the ProofWidgets release cache could not resolve its missing local Git tag. Project compilation, axiom auditing, type extraction, and proof-dependency auditing remained **NOT_RUN**. The subsequent v1.0.1 tooling fix preserves every Lean proof source and exact dependency commit.
