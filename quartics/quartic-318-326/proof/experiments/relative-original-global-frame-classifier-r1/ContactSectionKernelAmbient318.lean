module
public import ContactFiniteKernelCoordinates318
public import ContactAmbientTensorNaturality318
public import ContactAmbientInfinityPower318
public section
noncomputable section
namespace ContactSectionKernelAmbient318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open ContactOriginalRelativePolynomialCharts318 ContactOriginalRelativeLineOverlap318
open ContactOriginalCoefficientActions318 ContactCoefficientNativeSections318
open ContactRelativeWholeOpenSections318 ContactRelativeGeometricTwist318
open ContactRelativeFiniteCohomologyModel318 ContactOriginalSectionKernel318
open scoped TensorProduct
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ) (L : Line (curve R c))
local instance : Module R (finiteSections R c L) := finiteModule R c L
local instance : Module R (infinitySections R c L) := infinityModule R c L
local instance (N : Line (curve R c)) (U : (curve R c).Opens) : Module R Γ(N.object,U) :=
  OriginalCoefficientCohomology318.sectionModule R (ContactRelativeStructuralHOne318.projection R c) N U

lemma finite_pair (s : Γ(L.object,⊤)) :
    finiteEquiv R c L (ContactRelativeOriginalHZero318.pair R c L s).1 =
      L.object.presheaf.map (homOfLE (show finiteOpen R c≤⊤ from le_top)).op s :=
  (finiteEquiv R c L).apply_symm_apply _
lemma infinity_pair (s : Γ(L.object,⊤)) :
    infinityEquiv R c L (ContactRelativeOriginalHZero318.pair R c L s).2 =
      L.object.presheaf.map (homOfLE (show infinityOpen R c≤⊤ from le_top)).op s :=
  (infinityEquiv R c L).apply_symm_apply _

variable (S : CommRingCat.{0}) [Algebra ℚ S] (f : R →ₐ[ℚ] S)
local instance : Algebra R S := f.toAlgebra
local instance : Module S (finiteSections S c (L' R S f c L)) := finiteModule S c _
local instance : Module S (infinitySections S c (L' R S f c L)) := infinityModule S c _
local instance (N : Line (curve S c)) (U : (curve S c).Opens) : Module S Γ(N.object,U) :=
  OriginalCoefficientCohomology318.sectionModule S (ContactRelativeStructuralHOne318.projection S c) N U

lemma finite (x : LinearMap.ker ((boundary R c L).baseChange S)) :
    (L' R S f c L).object.presheaf.map (homOfLE (show finiteOpen S c≤⊤ from le_top)).op
      (sections R c L S f x) =
    ContactAmbientTensorNaturality318.finite R S f c L
      ((ContactTwistGlobalCoordinates318.finiteValue R c L ((bound R c L+1:ℕ):ℤ)).baseChange S x.val) := by
  have hi := congrArg Prod.fst (ContactFiniteKernelCoordinates318.inclusion S c (L' R S f c L)
    (bound R c L) (sections R c L S f x))
  rw [ContactOriginalSectionKernel318.sections_coordinate] at hi
  change ContactTwistGlobalCoordinates318.finiteValue S c (L' R S f c L) _
    (ContactFiniteComplexCoefficient318.zeroEquivalence R S f c L _ _ x.val)=
      (ContactRelativeOriginalHZero318.pair S c (L' R S f c L) _).1 at hi
  rw [ContactFiniteKernelCoordinates318.finite_tensor] at hi
  rw [← finite_pair]
  exact congrArg (finiteEquiv S c (L' R S f c L)) hi.symm

lemma infinity (x : LinearMap.ker ((boundary R c L).baseChange S)) :
    ContactAmbientInfinityPower318.power S c (L' R S f c L) (bound R c L)
      ((L' R S f c L).object.presheaf.map (homOfLE (show infinityOpen S c≤⊤ from le_top)).op
        (sections R c L S f x)) =
    ContactAmbientTensorNaturality318.infinity R S f c L
      ((ContactTwistGlobalCoordinates318.infinityValue R c L ((bound R c L+1:ℕ):ℤ)).baseChange S x.val) := by
  have hi := congrArg Prod.snd (ContactFiniteKernelCoordinates318.inclusion S c (L' R S f c L)
    (bound R c L) (sections R c L S f x))
  rw [ContactOriginalSectionKernel318.sections_coordinate] at hi
  change ContactTwistGlobalCoordinates318.infinityValue S c (L' R S f c L) _
    (ContactFiniteComplexCoefficient318.zeroEquivalence R S f c L _ _ x.val)=
      ContactRelativeInfinityJet318.power S c (L' R S f c L) _
        (ContactRelativeOriginalHZero318.pair S c (L' R S f c L) _).2 at hi
  rw [ContactFiniteKernelCoordinates318.infinity_tensor] at hi
  rw [← infinity_pair]
  change infinityEquiv S c _ (ContactRelativeInfinityJet318.power S c _ _
    ((infinityEquiv S c _).symm (infinityEquiv S c _ _)))=_
  rw [AddEquiv.symm_apply_apply]
  exact congrArg (infinityEquiv S c (L' R S f c L)) hi.symm
end ContactSectionKernelAmbient318
