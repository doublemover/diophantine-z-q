module
public import ArithmeticComparisonInjective318
public section
noncomputable section
namespace ArithmeticComparisonHomeomorph318
open ThreeArithmeticQuotient318 ArithmeticPointTopology318

lemma sourceMap_injective (N : ℕ) [NeZero N] : Function.Injective (sourceMap N) := by
  intro p q h
  exact ArithmeticComparisonInjective318.complexPoint_injective N (congrArg Points.hom h)

/-- The actual modular comparison is a homeomorphism onto the actual complex
points of the specified rank-four fixed algebra in their literal j,x topology.
This theorem does not construct an algebraic analytification or a PEL moduli object. -/
@[expose] def comparison (N : ℕ) [NeZero N] : Source ≃ₜ Points N :=
  (Equiv.ofBijective (sourceMap N) ⟨sourceMap_injective N,sourceMap_surjective N⟩).toHomeomorphOfContinuousClosed
     (sourceMap_continuous N) (sourceMap_proper N).isClosedMap

lemma comparison_hom (N : ℕ) [NeZero N] (q : Source) :
    (comparison N q).hom=complexPoint N q := rfl

lemma comparison_coordinates (N : ℕ) [NeZero N] (q : Source) :
    pointCoordinates N (comparison N q)=ModularCoordinateProper318.openCoordinates q :=
  sourceMap_coordinates N q

end ArithmeticComparisonHomeomorph318
