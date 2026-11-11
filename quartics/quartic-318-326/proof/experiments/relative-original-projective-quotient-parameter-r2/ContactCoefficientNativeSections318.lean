module
public import ContactOriginalCoefficientActions318
public import ContactCoefficientRestrictionSquares318
public section
noncomputable section
namespace ContactCoefficientNativeSections318
open AlgebraicGeometry CategoryTheory LineSheafClass318 TensorProduct
open ContactOriginalRelativePolynomialCharts318 ContactOriginalRelativeOverlap318
open ContactOriginalRelativeLineOverlap318 ContactOriginalCoefficientActions318
open scoped TensorProduct
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R S : CommRingCat.{0}) [Algebra ℚ R] [Algebra ℚ S]
  (f : R →ₐ[ℚ] S) (c : Fin 4 → ℚˣ) (L : Line (curve R c))
local instance : Algebra R S := f.toAlgebra
abbrev L' := ContactCoefficientLineCharts318.pulledLine R S f c L
local instance : Module R (finiteSections R c L) := finiteModule R c L
local instance : Module R (infinitySections R c L) := infinityModule R c L
local instance : Module R (originalSections R c L) := overlapModule R c L
local instance : Module S (finiteSections S c (L' R S f c L)) := finiteModule S c _
local instance : Module S (infinitySections S c (L' R S f c L)) := infinityModule S c _
local instance : Module S (originalSections S c (L' R S f c L)) := overlapModule S c _

/-- Actual coefficient extension for the ORIGINAL coefficient actions
used by the original Cech quotient, on each entire chart. -/
@[expose] def finiteEquivalence : S ⊗[R] finiteSections R c L ≃ₗ[S]
    finiteSections S c (L' R S f c L) :=
  (AlgebraTensorModule.congr (LinearEquiv.refl S S) (finiteIdentity R c L)).trans
    ((ContactCoefficientSectionEquivalences318.finiteEquivalence R S f c L).trans
      (finiteIdentity S c (L' R S f c L)).symm)
@[expose] def infinityEquivalence : S ⊗[R] infinitySections R c L ≃ₗ[S]
    infinitySections S c (L' R S f c L) :=
  (AlgebraTensorModule.congr (LinearEquiv.refl S S) (infinityIdentity R c L)).trans
    ((ContactCoefficientSectionEquivalences318.infinityEquivalence R S f c L).trans
      (infinityIdentity S c (L' R S f c L)).symm)
@[expose] def overlapEquivalence : S ⊗[R] originalSections R c L ≃ₗ[S]
    originalSections S c (L' R S f c L) :=
  (AlgebraTensorModule.congr (LinearEquiv.refl S S) (overlapIdentity R c L)).trans
    ((ContactCoefficientSectionEquivalences318.overlapEquivalence R S f c L).trans
      (overlapIdentity S c (L' R S f c L)).symm)

lemma finite_pure (s : S) (x : finiteSections R c L) :
    finiteEquivalence R S f c L (s ⊗ₜ[R] x) =
      s • ContactCoefficientLineCharts318.finiteRestriction R S f c L x := by
  change (finiteIdentity S c (L' R S f c L)).symm
    (OriginalCoefficientSections318.equivalence _ _ _ _ _ _ _ _ _
      (s ⊗ₜ[R] finiteIdentity R c L x)) = _
  rw [OriginalCoefficientSections318.pure_tensor,LinearEquiv.map_smul]
  rfl
lemma infinity_pure (s : S) (x : infinitySections R c L) :
    infinityEquivalence R S f c L (s ⊗ₜ[R] x) =
      s • ContactCoefficientLineCharts318.infinityRestriction R S f c L x := by
  change (infinityIdentity S c (L' R S f c L)).symm
    (OriginalCoefficientSections318.equivalence _ _ _ _ _ _ _ _ _
      (s ⊗ₜ[R] infinityIdentity R c L x)) = _
  rw [OriginalCoefficientSections318.pure_tensor,LinearEquiv.map_smul]
  rfl
lemma overlap_pure (s : S) (x : originalSections R c L) :
    overlapEquivalence R S f c L (s ⊗ₜ[R] x) =
      s • ContactCoefficientLineCharts318.overlapRestriction R S f c L x := by
  change (overlapIdentity S c (L' R S f c L)).symm
    (OriginalCoefficientSections318.equivalence _ _ _ _ _ _ _ _ _
      (s ⊗ₜ[R] overlapIdentity R c L x)) = _
  rw [OriginalCoefficientSections318.pure_tensor,LinearEquiv.map_smul]
  rfl
end ContactCoefficientNativeSections318
