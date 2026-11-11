module
public import ContactOriginalSectionKernel318
public import ContactTwistGlobalCoordinates318
public section
noncomputable section
namespace ContactFiniteKernelCoordinates318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open ContactOriginalRelativePolynomialCharts318 ContactOriginalRelativeLineOverlap318
open ContactOriginalCoefficientActions318 ContactCoefficientNativeSections318
open ContactRelativeGeometricTwist318 ContactRelativeFiniteCohomologyModel318
open scoped TensorProduct
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ)
  (L : Line (curve R c)) (b : ℕ)
local instance : Module R (finiteSections R c L) := finiteModule R c L
local instance : Module R (infinitySections R c L) := infinityModule R c L
local instance (N : Line (curve R c)) : Module R Γ(N.object,⊤) :=
  OriginalCoefficientCohomology318.sectionModule R (ContactRelativeStructuralHOne318.projection R c) N ⊤

/-- Exact original H0 inclusion: the finite coordinate is unchanged and the
infinity coordinate is multiplied by the actual original coordinate power. -/
lemma inclusion (s : Γ(L.object,⊤)) :
    (ContactRelativeTwistKernel318.globalEquivalence R c L ((b+1:ℕ):ℤ)
      (hzero R c L b s).val).val =
    ((ContactRelativeOriginalHZero318.pair R c L s).1,
      ContactRelativeInfinityJet318.power R c L b (ContactRelativeOriginalHZero318.pair R c L s).2) := by
  change (ContactRelativeTwistKernel318.globalEquivalence R c L ((b+1:ℕ):ℤ)
    ((ContactRelativeTwistKernel318.globalEquivalence R c L ((b+1:ℕ):ℤ)).symm _)).val=_
  rw [LinearEquiv.apply_symm_apply]
  rfl

variable (S : CommRingCat.{0}) [Algebra ℚ S] (f : R →ₐ[ℚ] S)
local instance : Algebra R S := f.toAlgebra
local instance : Module S (finiteSections S c (L' R S f c L)) := finiteModule S c _
local instance : Module S (infinitySections S c (L' R S f c L)) := infinityModule S c _
local instance (N : Line (curve S c)) : Module S Γ(N.object,⊤) :=
  OriginalCoefficientCohomology318.sectionModule S (ContactRelativeStructuralHOne318.projection S c) N ⊤
variable (hz : ∀ x : NonreducedLineMayerVietoris318.H1 (twist R c L ((b+1:ℕ):ℤ)),x=0)

lemma finite_tensor (z : S ⊗[R] termZero R c L b) :
    ContactTwistGlobalCoordinates318.finiteValue S c (L' R S f c L) ((b+1:ℕ):ℤ)
      (ContactFiniteComplexCoefficient318.zeroEquivalence R S f c L b hz z)=
    finiteEquivalence R S f c L
      ((ContactTwistGlobalCoordinates318.finiteValue R c L ((b+1:ℕ):ℤ)).baseChange S z) := by
  induction z using TensorProduct.inductionOn with
  | tmul s x =>
      have h := congrArg Prod.fst (ContactFiniteComplexCoefficient318.zero_coordinates R S f c L b hz s x)
      rw [ContactRelativeHZeroBaseChange318.pair_tmul] at h
      exact h
  | add z w hz hw => simp only [map_add,hz,hw]

lemma infinity_tensor (z : S ⊗[R] termZero R c L b) :
    ContactTwistGlobalCoordinates318.infinityValue S c (L' R S f c L) ((b+1:ℕ):ℤ)
      (ContactFiniteComplexCoefficient318.zeroEquivalence R S f c L b hz z)=
    infinityEquivalence R S f c L
      ((ContactTwistGlobalCoordinates318.infinityValue R c L ((b+1:ℕ):ℤ)).baseChange S z) := by
  induction z using TensorProduct.inductionOn with
  | tmul s x =>
      have h := congrArg Prod.snd (ContactFiniteComplexCoefficient318.zero_coordinates R S f c L b hz s x)
      rw [ContactRelativeHZeroBaseChange318.pair_tmul] at h
      exact h
  | add z w hz hw => simp only [map_add,hz,hw]
end ContactFiniteKernelCoordinates318
