# Original quotient classes with nonzero actual H1 residues

This86-source revision copies character-nonvanishing-r1 and changes only two
scalar-transport proof steps; all theorem statements are unchanged. The original
82-source chain and four connected nonvanishing modules remain in the closure. No local Lean build was run. Hosted strict elaboration,
recursive axiom auditing and independent acceptance remain pending.

OriginalSimplePoleResidues318 preserves a specified pole bound in the original
whole-overlap reduction. Every numerator divided by the original u has a unique
simple negative part plus an element of the whole original infinity ring.
Multiplication by actual u, injectivity of the original infinity-to-overlap map,
and evaluation of the original infinity basis at u=0 identify its first residue
with the corresponding coefficient at that point. This uses the residue map that
annihilates both whole chart images, not a field-level nonzero criterion.

InfinityBasisUnitCoefficients318 computes each original infinity basis square
in the original base ring. The resulting coefficient is a genuine unit. For the
four complementary-root characters the old ratioProduct is exactly the named
basis monomial, with no unproved normalization change.

OriginalCharacterSimplePole318 uses the literal quotient representative from the
preceding packet. Its actual whole-infinity numerator has polynomial
xScale^2*(c0-centroid*u^2)^2 and denominator unit
(yScale*c0^3)*(basis-square coefficient). Multiplying by the original coefficientUnit
proves the exact identity before passing through the original injective embeddings.
Thus the original source-ring representative is numerator/u. Its evaluated basis
coefficient is nonzero because xScale and c0 are original rational units and the
entire denominator is an original base-ring unit.

OriginalCharacterHOneNonzero318 applies the actual residueMap on source H1 to the
original characterPullback of the specified target cohomologyClass. The computed
coefficient is nonzero, proving both that pullback and that actual target class
nonzero, for all four original complementary-root maps. The final consumer joins
the earlier independently separated original images and dimension-five source:
only existence of a nonzero class in the fifth target remains as an explicit
input to bijectivity of the original five-pullback sum. This packet does not claim
that fifth input, unconditional five-map exhaustion, or identification of the
inverse with normalized transfers.

Revision2 addresses the exact c7d3bc3 hosted failure at whole principal reduction
line58: rewriting Algebra.smul_def did not infer the original displayed basis
module instance. A typed change exposes the same original algebraMap product
before map_mul. The identical new prescribed-reduction step is repaired too.
The failed82-source bytes and hosted artifact are preserved separately. All41
predecessors passed in that run; downstream elaboration remains pending.
