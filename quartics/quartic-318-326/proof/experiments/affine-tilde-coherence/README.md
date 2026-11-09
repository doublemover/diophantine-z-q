# Canonical affine tilde-pullback coherence

Five draft modules derive composition and identity coherence of the existing
`TildePullback318.pullbackIso` from its actual adjunction normalization.

- `AffineGlobalSectionCoherence318` compares the actual affine pushforward
  global sections with successive scalar restriction. Both maps act identically
  on underlying sections, while their actual scalar actions remain in the
  source and target. Composite and identity Spec equality transports are explicit.
- `TildePullbackMate318` identifies the exact existing canonical tilde pullback
  comparison as the conjugate of the inverse global-section comparison. The
  proof uses the original transported-right-adjoint construction and its unit.
- `AffineComparisonMates318` computes mates of the actual sheaf pullback
  composition, including Spec map equality transport, and scalar composition.
- `TildePullbackComposition318` uses conjugation injectivity and the global
  composition equation to equate the two actual tilde-pullback paths. All
  intermediate adjunctions and associators are shown explicitly.
- `TildePullbackIdentity318` proves the corresponding identity equation using
  the original sheaf identity comparison and scalar-extension identity map.

The final component equations retain the exact canonical pullback, tilde and
scalar-extension maps. They assume no cocycle, no coherence property, no scalar
normalization choice, no flatness and no reducedness. The objects are arbitrary
modules on arbitrary commutative rings at the fixed universe.

This is a prerequisite for the geometric sheaf-to-module overlap bridge. The
transport of an original geometric diagonal/triple equation through the
original line sections comparison is still further work. This packet does not
claim effective fppf descent, non-affine gluing, a represented Jacobian or the
full arithmetic theorem.

## Validation

The packet imports only accepted-baseline and pinned upstream sources. Its five
sources, dependencies, module order and recursive audit target are source-bound.
Static hash/import/placeholder checks pass. No local Lean compilation was run,
as instructed. Hosted strict compilation, recursive axiom auditing and
independent acceptance remain pending. A source-level argument or static check
is not a kernel-checked mathematical result.
