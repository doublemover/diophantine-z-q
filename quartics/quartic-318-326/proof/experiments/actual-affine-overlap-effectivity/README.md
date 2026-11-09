# Actual categorical-double affine effectivity

This58-source draft proves effective descent of an original line along a
faithfully flat map Spec S to Spec R, with the displayed reconstruction
isomorphism satisfying the original categorical-double compatibility square.
The inputs are the original sheaf overlap and its actual scheme diagonal and
triple equations. No tensor cocycle, coalgebra law or reconstruction
compatibility equation is a separate premise.

Four new sources complete the geometric comparison:
- SheafIsoTransport318 proves that pullback along an actual scheme isomorphism
  reflects sheaf-map equality, using the original inverse, composition and
  identity comparisons. Normalized transport preserves this and commutes with
  conjugation by a specified cover-sheaf isomorphism.
- CanonicalSheafOverlap318 constructs the canonical overlap of an original
  pulled-back sheaf on an actual common-base diagram and on the categorical
  double. Its compatibility with transport is derived from the original
  pullback associator, with both endpoint paths retained.
- ActualCanonicalOverlap318 identifies transport of the genuine double's
  canonical overlap along the original doubleIso with the previously computed
  canonical tensor-spectrum overlap.
- ActualAffineEffectiveComparison318 reflects the already derived canonical
  comparison equation back to the original double and supplies the actual base
  line, original pullback isomorphism and exact geometric compatibility square.

The53 unchanged producers are exact copies from the54-source canonical overlap
packet. AffineTripleCoordinateLaws318 has one typed tensor normalization repair:
run42580912976 passed16 predecessors before its rewrite could not see the tensor
scalar action through the twice-comonad carrier. The revised proof explicitly
states that same ordinary tensor equality and uses tensor scalar multiplication.
All statements and mathematical inputs are unchanged; exact failure is retained.

This establishes the source-level affine geometric effectivity consumer, not
yet a general non-affine fppf stack theorem or identification with Mathlib's
separately packaged descent category. Arbitrary base-chart compatibility,
covering-sheaf object gluing, rigidification descent and represented Picard/
Jacobian remain further work. The full arithmetic theorem is not claimed.

All sources, exact producers, failure evidence and nine application obligations
are bound. Static import/hash/placeholder and audit-history checks are required.
No local Lean ran. Full58 hosted strict replay, recursive axiom audit and
independent acceptance remain pending.
