module
public import CompletedAdditionInverse318
public import CompletedAdditionCommutative318
public section
noncomputable section
namespace CompletedLeftInverse318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open WeierstrassGluing318
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable {R:Type u} [CommRing R]
/-- The literal inverse-first input, not an abstract pointwise operation. -/
@[expose] def antiDiagonal (A B:R) : scheme A B ⟶ pullback (structureMap A B) (structureMap A B) :=
  pullback.lift (GluedNegation318.negation A B) (𝟙 _)
    (by simp only [GluedNegation318.negation_over_base,Category.id_comp])
@[reassoc] theorem antiDiagonal_fst (A B:R) :
    antiDiagonal A B ≫ pullback.fst _ _=GluedNegation318.negation A B := by simp [antiDiagonal]
@[reassoc] theorem antiDiagonal_snd (A B:R) :
    antiDiagonal A B ≫ pullback.snd _ _=𝟙 _ := by simp [antiDiagonal]
theorem antiDiagonal_eq_swap (A B:R) :
    antiDiagonal A B=CompletedAdditionInverse318.antiDiagonal A B ≫
      (pullbackSymmetry (structureMap A B) (structureMap A B)).hom := by
  apply pullback.hom_ext
  · simp only [antiDiagonal_fst,Category.assoc,pullbackSymmetry_hom_comp_fst,
      CompletedAdditionInverse318.antiDiagonal_snd]
  · simp only [antiDiagonal_snd,Category.assoc,pullbackSymmetry_hom_comp_snd,
      CompletedAdditionInverse318.antiDiagonal_fst]
/-- Actual global left-inverse identity over every commutative coefficient base. -/
theorem antiDiagonal_addition (A B:R) (hD:IsUnit (-16*(4*A^3+27*B^2))) :
    antiDiagonal A B ≫ CompletedAddition318.addition A B hD=structureMap A B ≫ infinity A B := by
  rw [antiDiagonal_eq_swap,Category.assoc,CompletedAdditionCommutative318.addition_commutative,
    CompletedAdditionInverse318.antiDiagonal_addition]
end CompletedLeftInverse318
