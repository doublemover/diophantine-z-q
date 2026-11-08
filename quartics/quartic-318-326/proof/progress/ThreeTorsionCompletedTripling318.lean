module
public import ThreeTorsionCompletedDoubling318
public import CompletedAdditionInverse318
public section
noncomputable section
namespace ThreeTorsionCompletedTripling318
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ThreeTorsionCompletedDoubling318
set_option maxHeartbeats 800000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {R:Type} [CommRing R] (A B:R) [Invertible (3:R)]
  (hD:IsUnit (-16*(4*A^3+27*B^2)))

/-- On the actual torsion subscheme the iterated-addition inputs are (-P,P),
namely the actual anti-diagonal applied to the actual negation. -/
theorem tripleInputs_eq :
    inclusion A B hD ≫ CompletedIteratedAddition318.tripleInputs A B hD =
      inclusion A B hD ≫ GluedNegation318.negation A B ≫ CompletedAdditionInverse318.antiDiagonal A B := by
  apply pullback.hom_ext
  · simp only [Category.assoc,CompletedIteratedAddition318.tripleInputs_fst,
      CompletedAdditionInverse318.antiDiagonal_fst,Category.comp_id]
    exact doubling_eq_negation A B hD
  · simp only [Category.assoc,CompletedIteratedAddition318.tripleInputs_snd,
      CompletedAdditionInverse318.antiDiagonal_snd,GluedNegation318.negation_twice,Category.comp_id]

/-- The entire relative rank-eight torsion scheme is killed by the actual
completed tripling composite. This is an equality of Scheme morphisms over
arbitrary bases, including nilpotents; a global kernel equality is not asserted. -/
theorem inclusion_tripling :
    inclusion A B hD ≫ CompletedIteratedAddition318.tripling A B hD =
      ThreeTorsionScheme318.structureMap A B hD ≫ WeierstrassGluing318.infinity A B := by
  rw [CompletedIteratedAddition318.tripling,←Category.assoc,tripleInputs_eq]
  simp only [Category.assoc,CompletedAdditionInverse318.antiDiagonal_addition]
  rw [←Category.assoc (GluedNegation318.negation A B)
    (WeierstrassGluing318.structureMap A B) (WeierstrassGluing318.infinity A B),
    GluedNegation318.negation_over_base,←Category.assoc,inclusion_over_base]
end ThreeTorsionCompletedTripling318
