module
public import ContactFlatHZeroBaseChange318
public import ContactHZeroGeometricUnit318
public section
noncomputable section
namespace ContactFlatHZeroGeometric318
open AlgebraicGeometry CategoryTheory LineSheafClass318 TensorProduct
open ContactOriginalRelativePolynomialCharts318 ContactOriginalRelativeLineOverlap318
open ContactOriginalCoefficientActions318 ContactCoefficientNativeSections318
open ContactRelativeCoefficientChange318 OriginalSectionPullbackComposition318
open scoped TensorProduct
variable (R S : CommRingCat.{0}) [Algebra ℚ R] [Algebra ℚ S]
  (f : R →ₐ[ℚ] S) (c : Fin 4 → ℚˣ) (L : Line (curve R c))
local instance : Algebra R S := f.toAlgebra
local instance : Module R Γ(L.object,⊤) :=
  OriginalCoefficientCohomology318.sectionModule R (ContactRelativeStructuralHOne318.projection R c) L ⊤
local instance : Module S Γ((L' R S f c L).object,⊤) :=
  OriginalCoefficientCohomology318.sectionModule S (ContactRelativeStructuralHOne318.projection S c) _ ⊤
local instance : Module R (finiteSections R c L) := finiteModule R c L
local instance : Module R (infinitySections R c L) := infinityModule R c L
local instance : Module S (finiteSections S c (L' R S f c L)) := finiteModule S c _
local instance : Module S (infinitySections S c (L' R S f c L)) := infinityModule S c _
variable [Module.Flat R S]

/-- The flat H0 comparison uses the ACTUAL geometric pullback unit on
every original section, proved on both complete original chart coordinates. -/
lemma unit (s : Γ(L.object,⊤)) :
    ContactFlatHZeroBaseChange318.equivalence R S f c L ((1:S) ⊗ₜ[R] s)=
      pull (curveMap R S f c) L.object s := by
  apply ContactRelativeOriginalHZero318.injective S c (L' R S f c L)
  apply Subtype.ext
  change ContactRelativeOriginalHZero318.pair S c (L' R S f c L) _ =
    ContactRelativeOriginalHZero318.pair S c (L' R S f c L) _
  rw [ContactFlatHZeroBaseChange318.coordinates,ContactFlatHZeroBaseChange318.pair_tmul,
    finite_pure,infinity_pure,one_smul,one_smul,ContactHZeroGeometricUnit318.geometric_coordinates]

lemma pure_tensor (a : S) (s : Γ(L.object,⊤)) :
    ContactFlatHZeroBaseChange318.equivalence R S f c L (a ⊗ₜ[R] s)=
      a • pull (curveMap R S f c) L.object s := by
  have ht : a ⊗ₜ[R] s=a • ((1:S) ⊗ₜ[R] s) := by rw [smul_tmul',smul_eq_mul,mul_one]
  rw [ht,map_smul,unit]
end ContactFlatHZeroGeometric318
