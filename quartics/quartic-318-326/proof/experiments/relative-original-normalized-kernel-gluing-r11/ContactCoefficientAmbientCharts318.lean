module
public import ContactCoefficientAmbientUnit318
public import ContactRelativeCoefficientWholeSections318
public import ContactCoefficientNativeSections318
public import OriginalOpenSectionNaturality318
public section
noncomputable section
namespace ContactCoefficientAmbientCharts318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open ContactOriginalRelativePolynomialCharts318 ContactOriginalRelativeLineOverlap318
open ContactOriginalCoefficientActions318 ContactCoefficientNativeSections318
open ContactRelativeWholeOpenSections318 ContactRelativeCoefficientChange318
open OriginalSectionTransport318
open scoped TensorProduct
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R S : CommRingCat.{0}) [Algebra ℚ R] [Algebra ℚ S]
  (f : R →ₐ[ℚ] S) (c : Fin 4 → ℚˣ) (L : Line (curve R c))
local instance : Algebra R S := f.toAlgebra
local instance (N : Line (curve R c)) (U : (curve R c).Opens) : Module R Γ(N.object,U) :=
  OriginalCoefficientCohomology318.sectionModule R (ContactRelativeStructuralHOne318.projection R c) N U
local instance (N : Line (curve S c)) (U : (curve S c).Opens) : Module S Γ(N.object,U) :=
  OriginalCoefficientCohomology318.sectionModule S (ContactRelativeStructuralHOne318.projection S c) N U
local instance : Module R (finiteSections R c L) := finiteModule R c L
local instance : Module S (finiteSections S c (L' R S f c L)) := finiteModule S c _

lemma finite_square (s : finiteSections R c L) :
    finiteEquiv S c (L' R S f c L)
      (ContactCoefficientLineCharts318.finiteRestriction R S f c L s) =
    pullTo (curveMap R S f c) L.object (finiteOpen R c) (finiteOpen S c)
      (ContactCoefficientWholeOpens318.finite_preimage R S f c) (finiteEquiv R c L s) := by
  change OriginalOpenPullbackSections318.sectionsEquiv (finiteInto S c) _
    (OriginalAffineLinePathSections318.restriction (finiteRingMap R S f c) _ _ _ s)=_
  rw [OriginalAffinePathWholeSections318.restriction_direct]
  exact OriginalWholeOpenCoefficientSquare318.square (curveMap R S f c)
    (finiteInto R c) (finiteInto S c) (Spec.map (finiteRingMap R S f c))
    (ContactRelativeCoefficientChange318.finite_square R S f c)
    (ContactCoefficientWholeOpens318.finite_preimage R S f c) L.object s

lemma finite_unit (x : finiteSections R c L) :
    ContactRelativeCoefficientWholeSections318.finiteEquivalence S c (L' R S f c L)
      (finiteEquivalence R S f c L ((1:S) ⊗ₜ[R] x)) =
    pullTo (curveMap R S f c) L.object (finiteOpen R c) (finiteOpen S c)
      (ContactCoefficientWholeOpens318.finite_preimage R S f c)
      (ContactRelativeCoefficientWholeSections318.finiteEquivalence R c L x) := by
  rw [finite_pure,one_smul]
  exact finite_square R S f c L x

/-- Structural-coefficient semilinearity on the entire actual finite open;
proved through the genuine chart base change, without H1 vanishing. -/
lemma finite_smul (a : R) (s : Γ(L.object,finiteOpen R c)) :
    pullTo (curveMap R S f c) L.object (finiteOpen R c) (finiteOpen S c)
      (ContactCoefficientWholeOpens318.finite_preimage R S f c) (a • s) =
    f a • pullTo (curveMap R S f c) L.object (finiteOpen R c) (finiteOpen S c)
      (ContactCoefficientWholeOpens318.finite_preimage R S f c) s := by
  obtain ⟨x,rfl⟩ := (ContactRelativeCoefficientWholeSections318.finiteEquivalence R c L).surjective s
  rw [← LinearEquiv.map_smul,← finite_unit,← finite_unit]
  have ht : (1:S) ⊗ₜ[R] (a • x)=f a • ((1:S) ⊗ₜ[R] x) := by
    rw [TensorProduct.tmul_smul,TensorProduct.smul_tmul',TensorProduct.smul_tmul']
    change (f a*1) ⊗ₜ[R] x=(f a*1) ⊗ₜ[R] x
    rfl
  rw [ht,LinearEquiv.map_smul,LinearEquiv.map_smul]
local instance : Module R (infinitySections R c L) := infinityModule R c L
local instance : Module S (infinitySections S c (L' R S f c L)) := infinityModule S c _

lemma infinity_square (s : infinitySections R c L) :
    infinityEquiv S c (L' R S f c L)
      (ContactCoefficientLineCharts318.infinityRestriction R S f c L s) =
    pullTo (curveMap R S f c) L.object (infinityOpen R c) (infinityOpen S c)
      (ContactCoefficientWholeOpens318.infinity_preimage R S f c) (infinityEquiv R c L s) := by
  change OriginalOpenPullbackSections318.sectionsEquiv (infinityInto S c) _
    (OriginalAffineLinePathSections318.restriction (infinityRingMap R S f c) _ _ _ s)=_
  rw [OriginalAffinePathWholeSections318.restriction_direct]
  exact OriginalWholeOpenCoefficientSquare318.square (curveMap R S f c)
    (infinityInto R c) (infinityInto S c) (Spec.map (infinityRingMap R S f c))
    (ContactRelativeCoefficientChange318.infinity_square R S f c)
    (ContactCoefficientWholeOpens318.infinity_preimage R S f c) L.object s

lemma infinity_unit (x : infinitySections R c L) :
    ContactRelativeCoefficientWholeSections318.infinityEquivalence S c (L' R S f c L)
      (infinityEquivalence R S f c L ((1:S) ⊗ₜ[R] x)) =
    pullTo (curveMap R S f c) L.object (infinityOpen R c) (infinityOpen S c)
      (ContactCoefficientWholeOpens318.infinity_preimage R S f c)
      (ContactRelativeCoefficientWholeSections318.infinityEquivalence R c L x) := by
  rw [infinity_pure,one_smul]
  exact infinity_square R S f c L x

/-- Structural-coefficient semilinearity on the entire actual infinity open;
proved through the genuine chart base change, without H1 vanishing. -/
lemma infinity_smul (a : R) (s : Γ(L.object,infinityOpen R c)) :
    pullTo (curveMap R S f c) L.object (infinityOpen R c) (infinityOpen S c)
      (ContactCoefficientWholeOpens318.infinity_preimage R S f c) (a • s) =
    f a • pullTo (curveMap R S f c) L.object (infinityOpen R c) (infinityOpen S c)
      (ContactCoefficientWholeOpens318.infinity_preimage R S f c) s := by
  obtain ⟨x,rfl⟩ := (ContactRelativeCoefficientWholeSections318.infinityEquivalence R c L).surjective s
  rw [← LinearEquiv.map_smul,← infinity_unit,← infinity_unit]
  have ht : (1:S) ⊗ₜ[R] (a • x)=f a • ((1:S) ⊗ₜ[R] x) := by
    rw [TensorProduct.tmul_smul,TensorProduct.smul_tmul',TensorProduct.smul_tmul']
    change (f a*1) ⊗ₜ[R] x=(f a*1) ⊗ₜ[R] x
    rfl
  rw [ht,LinearEquiv.map_smul,LinearEquiv.map_smul]
end ContactCoefficientAmbientCharts318
