module
public import CompletedAddition318
public section
noncomputable section
namespace CompletedIteratedAddition318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open WeierstrassGluing318
set_option maxHeartbeats 800000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable {R:Type u} [CommRing R]
@[expose] def diagonal (A B:R) : scheme A B ⟶ pullback (structureMap A B) (structureMap A B) :=
  pullback.lift (𝟙 _) (𝟙 _) rfl
@[reassoc] theorem diagonal_fst (A B:R) : diagonal A B ≫ pullback.fst _ _=𝟙 _ := by simp [diagonal]
@[reassoc] theorem diagonal_snd (A B:R) : diagonal A B ≫ pullback.snd _ _=𝟙 _ := by simp [diagonal]
/-- Actual doubling composite. Its group-theoretic interpretation is a separate endpoint. -/
@[expose] def doubling (A B:R) (hD:IsUnit (-16*(4*A^3+27*B^2))) : scheme A B ⟶ scheme A B :=
  diagonal A B ≫ CompletedAddition318.addition A B hD
@[reassoc] theorem doubling_over_base (A B:R) (hD:IsUnit (-16*(4*A^3+27*B^2))) :
    doubling A B hD ≫ structureMap A B=structureMap A B := by
  rw [doubling,Category.assoc,CompletedAddition318.addition_over_base,diagonal_fst_assoc]
@[expose] def tripleInputs (A B:R) (hD:IsUnit (-16*(4*A^3+27*B^2))) :
    scheme A B ⟶ pullback (structureMap A B) (structureMap A B) :=
  pullback.lift (doubling A B hD) (𝟙 _) (by rw [doubling_over_base,Category.id_comp])
@[reassoc] theorem tripleInputs_fst (A B:R) (hD:IsUnit (-16*(4*A^3+27*B^2))) :
    tripleInputs A B hD ≫ pullback.fst _ _=doubling A B hD := by simp [tripleInputs]
@[reassoc] theorem tripleInputs_snd (A B:R) (hD:IsUnit (-16*(4*A^3+27*B^2))) :
    tripleInputs A B hD ≫ pullback.snd _ _=𝟙 _ := by simp [tripleInputs]
/-- Actual iterated-addition morphism P ↦ (P + P) + P. No group axiom is assumed in this definition. -/
@[expose] def tripling (A B:R) (hD:IsUnit (-16*(4*A^3+27*B^2))) : scheme A B ⟶ scheme A B :=
  tripleInputs A B hD ≫ CompletedAddition318.addition A B hD
@[reassoc] theorem tripling_over_base (A B:R) (hD:IsUnit (-16*(4*A^3+27*B^2))) :
    tripling A B hD ≫ structureMap A B=structureMap A B := by
  rw [tripling,Category.assoc,CompletedAddition318.addition_over_base,tripleInputs_fst_assoc,doubling_over_base]
end CompletedIteratedAddition318
