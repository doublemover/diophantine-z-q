module
public import ContactSectionKernelAmbient318
public section
noncomputable section
namespace ContactSectionKernelGeometric318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open ContactOriginalRelativePolynomialCharts318 ContactOriginalRelativeLineOverlap318
open ContactOriginalCoefficientActions318 ContactCoefficientNativeSections318
open ContactRelativeWholeOpenSections318 ContactRelativeCoefficientChange318
open ContactOriginalSectionKernel318 OriginalSectionPullbackComposition318
open scoped TensorProduct
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R S T : CommRingCat.{0}) [Algebra ℚ R] [Algebra ℚ S] [Algebra ℚ T]
  (f : R →ₐ[ℚ] S) (g : S →ₐ[ℚ] T) (c : Fin 4 → ℚˣ) (L : Line (curve R c))
local instance : Algebra R S := f.toAlgebra
local instance : Algebra R T := (g.comp f).toAlgebra
local instance : Module R (finiteSections R c L) := finiteModule R c L
local instance : Module R (infinitySections R c L) := infinityModule R c L
local instance : Module S (finiteSections S c (L' R S f c L)) := finiteModule S c _
local instance : Module S (infinitySections S c (L' R S f c L)) := infinityModule S c _
local instance : Module T (finiteSections T c (L' R T (g.comp f) c L)) := finiteModule T c _
local instance : Module T (infinitySections T c (L' R T (g.comp f) c L)) := infinityModule T c _
local instance (N : Line (curve R c)) : Module R Γ(N.object,⊤) :=
  OriginalCoefficientCohomology318.sectionModule R (ContactRelativeStructuralHOne318.projection R c) N ⊤
local instance (N : Line (curve S c)) (U : (curve S c).Opens) : Module S Γ(N.object,U) :=
  OriginalCoefficientCohomology318.sectionModule S (ContactRelativeStructuralHOne318.projection S c) N U
local instance (N : Line (curve T c)) (U : (curve T c).Opens) : Module T Γ(N.object,U) :=
  OriginalCoefficientCohomology318.sectionModule T (ContactRelativeStructuralHOne318.projection T c) N U

/-- Actual geometric pullback of EVERY kernel-realized original section agrees
with actual tensor coefficient transport. Both entire original charts are checked;
on infinity the genuine injective coordinate power is canceled, not divided formally. -/
lemma natural (x : LinearMap.ker ((boundary R c L).baseChange S)) :
    ContactHZeroCoefficientFunctor318.compositionSections R S f c L T g
      (pull (curveMap S T g c) (L' R S f c L).object (sections R c L S f x)) =
    sections R c L T (g.comp f)
      (ProjectiveKernelNaturality318.transport R (zeroTerm R c L) (oneTerm R c L)
        (boundary R c L) S (ContactHZeroCoefficientFunctor318.coefficientArrow R S f T g) x) := by
  apply ContactRelativeOriginalHZero318.injective T c (L' R T (g.comp f) c L)
  apply Subtype.ext
  change ContactRelativeOriginalHZero318.pair T c (L' R T (g.comp f) c L) _ =
    ContactRelativeOriginalHZero318.pair T c (L' R T (g.comp f) c L) _
  apply Prod.ext
  · apply (finiteEquiv T c (L' R T (g.comp f) c L)).injective
    rw [ContactSectionKernelAmbient318.finite_pair,ContactSectionKernelAmbient318.finite_pair]
    rw [← ContactAmbientCoefficientComposition318.finite_restriction,
      ContactSectionKernelAmbient318.finite,ContactAmbientTensorNaturality318.finite_natural,
      ContactSectionKernelAmbient318.finite]
    apply congrArg (ContactAmbientTensorNaturality318.finite R T (g.comp f) c L)
    exact (ProjectiveKernelNaturality318.transport_square R (zeroTerm R c L)
      (finiteSections R c L)
      (ContactTwistGlobalCoordinates318.finiteValue R c L ((bound R c L+1:ℕ):ℤ)) S
      (ContactHZeroCoefficientFunctor318.coefficientArrow R S f T g) x.val).symm
  · apply (infinityEquiv T c (L' R T (g.comp f) c L)).injective
    rw [ContactSectionKernelAmbient318.infinity_pair,ContactSectionKernelAmbient318.infinity_pair]
    apply ContactAmbientInfinityPower318.injective T c (L' R T (g.comp f) c L) (bound R c L)
    rw [← ContactAmbientCoefficientComposition318.infinity_restriction,
      ← ContactAmbientInfinityPower318.composition,
      ContactSectionKernelAmbient318.infinity,ContactAmbientTensorNaturality318.infinity_natural,
      ContactSectionKernelAmbient318.infinity]
    apply congrArg (ContactAmbientTensorNaturality318.infinity R T (g.comp f) c L)
    exact (ProjectiveKernelNaturality318.transport_square R (zeroTerm R c L)
      (infinitySections R c L)
      (ContactTwistGlobalCoordinates318.infinityValue R c L ((bound R c L+1:ℕ):ℤ)) S
      (ContactHZeroCoefficientFunctor318.coefficientArrow R S f T g) x.val).symm
end ContactSectionKernelGeometric318
