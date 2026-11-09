# Exact canonical overlap compatibility of affine reconstruction

This54-source draft closes the tensor-spectrum reconstruction comparison square.
The displayed original pullback isomorphism is now proved to intertwine the
canonical overlap of the reconstructed base line with the unchanged input
sheaf overlap. This strengthens recovery of a coaction to an exact geometric
sheaf equation, using no additional compatibility assumption.

Four new modules carry the connected calculation:
- CanonicalScalarOverlap318 computes the full canonical overlap of a scalar
  extension through both original scalar-composition isomorphisms. Its original
  overlap-to-coaction equivalence gives precisely scalar extension of the
  original adjunction unit. Conjugation keeps the specified module comparison.
- CanonicalTildeOverlap318 identifies this scalar overlap with the canonical
  sheaf overlap using the actual tilde pullback comparison, its proved
  composition law, and both original endpoint naturality squares.
- CanonicalGeometricOverlap318 passes the resulting exact sheaf equation through
  the original sheaf-to-module equivalence and retains the specified original
  sections module and comparison at every endpoint.
- ReconstructedOverlapCompatibility318 specializes to the actual reconstructed
  coalgebra, proves that its displayed comparison is exactly that canonical
  comparison, and uses the existing proved coaction recovery plus injectivity
  to recover the original sheaf overlap and the commuting square.

The50-source actual scheme fiber-product reconstruction remains included.
Forty-nine predecessor sources are byte-identical to actual-geometric-affine-
descent-r2. ActualAffineDoubleNerve318 adds only the TensorProduct namespace
opening needed to parse its already stated diagonal tensor type. Exact hosted
failure42579994089 is retained. The previous missing comonad-definition import
repair is retained unchanged from r2.

The new compatibility theorem lives on the actual double tensor spectrum with
its actual Spec projection maps, not yet on the categorical fiber product.
Transport back along the retained doubleIso, identification with general
geometric descent categories, arbitrary base-chart gluing and non-affine
cover effectivity remain further work. No representable Picard/Jacobian or
full arithmetic theorem follows merely from this packet.

Static source/import/hash checks and the audit-history self-test are required.
No local Lean compilation is run. Complete54-source hosted replay, recursive
axiom audit and independent acceptance remain pending.
