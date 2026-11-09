# Affine overlap cocycle to original coassociativity

Five draft modules complete a module-level conversion that the retained
candidate-coaction packet left open:

- `AffineTripleCoactionCoordinates318` identifies the actual third vertex
  module on `S ⊗[R] (S ⊗[R] S)` with the twice-applied original scalar-extension
  comonad. Its formula retains all three coefficients and the module element.
- `AffineTripleOverlapMaps318` defines the three overlap edge maps by actual
  scalar pullback, conjugated by the canonical scalar-composition comparisons.
- `AffineTripleCoordinateLaws318` proves that the 13 edge becomes original
  comultiplication and the 12-then-23 composite becomes the original comonad
  map of the candidate coaction. These are tensor-induction proofs, not
  coassociativity hypotheses supplied under other names.
- `AffineOverlapCoassociativity318` evaluates the actual triple cocycle at
  unit tensors, obtaining coassociativity of the existing
  `AffineOverlapCoaction318.homEquiv`. Together with the retained diagonal
  calculation, it constructs an actual original-adjunction coalgebra.
- `AffineCocycleLine318` feeds that coalgebra directly into the retained
  faithfully flat rank-one reconstruction. The resulting actual line pulls
  back to the original covering line, and the module comparison retains the
  exact original coaction equation.

No replacement module or rank hypothesis is introduced in the final consumer:
the covering module is the original section module of the supplied original
line on `Spec S`. Faithful flatness is needed only for reconstruction, not
for the cocycle-to-coassociativity conversion.

## Scope boundary

The input cocycle is on the actual scalar-extended **modules**. The earlier
`OriginalLineOverlapCoaction318` gives a correspondence from geometric overlap
sheaf morphisms to these module morphisms, but compatibility of that
correspondence with the geometric diagonal and threefold pullback comparisons
is not proved here. In particular this packet does not claim that an arbitrary
geometric fppf matching family has already supplied its input hypotheses.
Arbitrary-scheme gluing, rigidification gluing, identification with the
associated fppf sheaf, degree zero and representability remain separate.

## Validation

The nineteen-source packet has five new sources and fourteen byte-identical
producer copies. Eight copies come from retained unfinished scalar/basechange
packets; their partial historical logs are not accepted as completed checks.
Source/hash/import/placeholder validation passes. Local Lean compilation was
not run, as instructed. Hosted strict replay, recursive axiom audit and
independent source acceptance are pending for the complete packet. No
unconditional arithmetic theorem is claimed.
