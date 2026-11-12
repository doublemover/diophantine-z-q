module
public import ContactRelativeHZeroBaseChange318
public import OriginalCoefficientGlobalUnit318
public section
noncomputable section
namespace ContactHZeroGeometricUnit318
open AlgebraicGeometry CategoryTheory LineSheafClass318 TensorProduct
open ContactOriginalRelativePolynomialCharts318 ContactOriginalRelativeLineOverlap318
open ContactOriginalCoefficientActions318 ContactCoefficientNativeSections318
open ContactRelativeCoefficientChange318 OriginalSectionPullbackComposition318
open scoped TensorProduct
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ) (L : Line (curve R c))
local instance : Module R Γ(L.object,⊤) :=
  OriginalCoefficientCohomology318.sectionModule R (ContactRelativeStructuralHOne318.projection R c) L ⊤
local instance : Module R (finiteSections R c L) := finiteModule R c L
local instance : Module R (infinitySections R c L) := infinityModule R c L

lemma finite_pair (s : Γ(L.object,⊤)) : (ContactRelativeOriginalHZero318.pair R c L s).1 =
    pull (finiteInto R c) L.object s := by
  apply (ContactRelativeWholeOpenSections318.finiteEquiv R c L).injective
  change (ContactRelativeWholeOpenSections318.finiteEquiv R c L)
      ((ContactRelativeWholeOpenSections318.finiteEquiv R c L).symm
        (L.object.presheaf.map (homOfLE le_top).op s)) = _
  rw [AddEquiv.apply_symm_apply]
  exact (OriginalOpenPullbackSections318.unit_sections (finiteInto R c) L.object s).symm
lemma infinity_pair (s : Γ(L.object,⊤)) : (ContactRelativeOriginalHZero318.pair R c L s).2 =
    pull (infinityInto R c) L.object s := by
  apply (ContactRelativeWholeOpenSections318.infinityEquiv R c L).injective
  change (ContactRelativeWholeOpenSections318.infinityEquiv R c L)
      ((ContactRelativeWholeOpenSections318.infinityEquiv R c L).symm
        (L.object.presheaf.map (homOfLE le_top).op s)) = _
  rw [AddEquiv.apply_symm_apply]
  exact (OriginalOpenPullbackSections318.unit_sections (infinityInto R c) L.object s).symm

variable (S : CommRingCat.{0}) [Algebra ℚ S] (f : R →ₐ[ℚ] S)
local instance : Algebra R S := f.toAlgebra
local instance : Module S Γ((L' R S f c L).object,⊤) :=
  OriginalCoefficientCohomology318.sectionModule S (ContactRelativeStructuralHOne318.projection S c)
    (L' R S f c L) ⊤
local instance : Module S (finiteSections S c (L' R S f c L)) := finiteModule S c _
local instance : Module S (infinitySections S c (L' R S f c L)) := infinityModule S c _

lemma geometric_coordinates (s : Γ(L.object,⊤)) :
    ContactRelativeOriginalHZero318.pair S c (L' R S f c L) (pull (curveMap R S f c) L.object s) =
    (ContactCoefficientLineCharts318.finiteRestriction R S f c L
        (ContactRelativeOriginalHZero318.pair R c L s).1,
      ContactCoefficientLineCharts318.infinityRestriction R S f c L
        (ContactRelativeOriginalHZero318.pair R c L s).2) := by
  apply Prod.ext
  · rw [finite_pair,finite_pair]
    exact (OriginalCoefficientGlobalUnit318.square (curveMap R S f c)
      (finiteRingMap R S f c) (finiteInto R c) (finiteInto S c)
      (ContactRelativeCoefficientChange318.finite_square R S f c) L s).symm
  · rw [infinity_pair,infinity_pair]
    exact (OriginalCoefficientGlobalUnit318.square (curveMap R S f c)
      (infinityRingMap R S f c) (infinityInto R c) (infinityInto S c)
      (ContactRelativeCoefficientChange318.infinity_square R S f c) L s).symm

/-- The earlier tensor H0 comparison is now identified with the actual
independently defined geometric unit on EVERY original global section.
This is the map identity needed for universal-section specialization. -/
lemma unit (hz : ∀ x : NonreducedLineMayerVietoris318.H1 L,x=0) (s : Γ(L.object,⊤)) :
    ContactRelativeHZeroBaseChange318.equivalence R S f c L hz ((1:S) ⊗ₜ[R] s) =
      pull (curveMap R S f c) L.object s := by
  apply ContactRelativeOriginalHZero318.injective S c (L' R S f c L)
  apply Subtype.ext
  change ContactRelativeOriginalHZero318.pair S c (L' R S f c L) _ =
    ContactRelativeOriginalHZero318.pair S c (L' R S f c L) _
  rw [ContactRelativeHZeroBaseChange318.coordinates,ContactRelativeHZeroBaseChange318.pair_tmul,
    finite_pure,infinity_pure,one_smul,one_smul,geometric_coordinates]

lemma pure_tensor (hz : ∀ x : NonreducedLineMayerVietoris318.H1 L,x=0)
    (a : S) (s : Γ(L.object,⊤)) :
    ContactRelativeHZeroBaseChange318.equivalence R S f c L hz (a ⊗ₜ[R] s) =
      a • pull (curveMap R S f c) L.object s := by
  have ht : a ⊗ₜ[R] s = a • ((1:S) ⊗ₜ[R] s) := by rw [smul_tmul',smul_eq_mul,mul_one]
  rw [ht,map_smul,unit]
end ContactHZeroGeometricUnit318
