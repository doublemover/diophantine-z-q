module
public import ContactPositiveKernelCoefficient318
public import EndomorphismCokernelBaseChange318
public import ContactRelativeFiniteCechComparison318
public section
noncomputable section
namespace ContactFiniteComplexCoefficient318
open AlgebraicGeometry CategoryTheory LineSheafClass318 TensorProduct
open ContactOriginalRelativePolynomialCharts318 ContactOriginalRelativeLineOverlap318
open ContactOriginalCoefficientActions318 ContactCoefficientNativeSections318
open ContactRelativeGeometricTwist318 ContactRelativeFiniteCohomologyModel318
open scoped TensorProduct
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R S : CommRingCat.{0}) [Algebra ℚ R] [Algebra ℚ S]
  (f : R →ₐ[ℚ] S) (c : Fin 4 → ℚˣ) (L : Line (curve R c)) (b : ℕ)
local instance : Algebra R S := f.toAlgebra
local instance : Module R (finiteSections R c L) := finiteModule R c L
local instance : Module R (infinitySections R c L) := infinityModule R c L
local instance : Module R (originalSections R c L) := overlapModule R c L
local instance : Module S (finiteSections S c (L' R S f c L)) := finiteModule S c _
local instance : Module S (infinitySections S c (L' R S f c L)) := infinityModule S c _
local instance : Module S (originalSections S c (L' R S f c L)) := overlapModule S c _
local instance (N : Line (curve R c)) : Module R Γ(N.object,⊤) :=
  OriginalCoefficientCohomology318.sectionModule R (ContactRelativeStructuralHOne318.projection R c) N ⊤
local instance (N : Line (curve S c)) : Module S Γ(N.object,⊤) :=
  OriginalCoefficientCohomology318.sectionModule S (ContactRelativeStructuralHOne318.projection S c) N ⊤

/-- The exact original infinity-jet base-change equivalence. -/
@[expose] def oneEquivalence : S ⊗[R] termOne R c L b ≃ₗ[S] termOne S c (L' R S f c L) b :=
  EndomorphismCokernelBaseChange318.equivalence S
    (ContactRelativeInfinityJet318.power R c L b) (ContactRelativeInfinityJet318.power S c (L' R S f c L) b)
    (infinityEquivalence R S f c L) (ContactCoefficientCoordinatePowers318.infinity_square R S f c L b)

lemma one_pure (s : S) (x : infinitySections R c L) :
    oneEquivalence R S f c L b (s ⊗ₜ[R] (ContactRelativeInfinityJet318.power R c L b).range.mkQ x)=
      (ContactRelativeInfinityJet318.power S c (L' R S f c L) b).range.mkQ
        (infinityEquivalence R S f c L (s ⊗ₜ[R] x)) :=
  EndomorphismCokernelBaseChange318.pure_tensor _ _ _ _ _ s x

variable (hz : ∀ x : NonreducedLineMayerVietoris318.H1 (twist R c L ((b+1 : ℕ) : ℤ)),x=0)

/-- Both terms use original structural actions. The freshly clutched S
twist is joined through its ACTUAL full-chart kernel, rather than silently
identifying it with an unrelated geometric pullback. -/
@[expose] def zeroEquivalence : S ⊗[R] termZero R c L b ≃ₗ[S] termZero S c (L' R S f c L) b :=
  (AlgebraTensorModule.congr (LinearEquiv.refl S S)
    (ContactRelativeTwistKernel318.globalEquivalence R c L ((b+1 : ℕ) : ℤ))).trans
    ((ContactPositiveKernelCoefficient318.equivalence R S f c L ((b+1 : ℕ) : ℤ) hz).trans
      (ContactRelativeTwistKernel318.globalEquivalence S c (L' R S f c L) ((b+1 : ℕ) : ℤ)).symm)

lemma zero_coordinates (s : S) (x : termZero R c L b) :
    (ContactRelativeTwistKernel318.globalEquivalence S c (L' R S f c L) ((b+1 : ℕ) : ℤ)
      (zeroEquivalence R S f c L b hz (s ⊗ₜ[R] x))).val =
    ContactRelativeHZeroBaseChange318.pairEquivalence R S f c L
      (s ⊗ₜ[R] (ContactRelativeTwistKernel318.globalEquivalence R c L ((b+1 : ℕ) : ℤ) x).val) := by
  change (ContactRelativeTwistKernel318.globalEquivalence S c (L' R S f c L) ((b+1 : ℕ) : ℤ)
    ((ContactRelativeTwistKernel318.globalEquivalence S c (L' R S f c L) ((b+1 : ℕ) : ℤ)).symm
      (ContactPositiveKernelCoefficient318.equivalence R S f c L ((b+1 : ℕ) : ℤ) hz
        (s ⊗ₜ[R] ContactRelativeTwistKernel318.globalEquivalence R c L ((b+1 : ℕ) : ℤ) x)))).val=_
  rw [LinearEquiv.apply_symm_apply]
  rfl

/-- The ACTUAL finite-complex differential commutes with every
coefficient extension, on the original whole infinity jet. -/
lemma differential_square : (differential S c (L' R S f c L) b).comp
    (zeroEquivalence R S f c L b hz).toLinearMap =
    (oneEquivalence R S f c L b).toLinearMap.comp ((differential R c L b).baseChange S) := by
  apply AlgebraTensorModule.ext
  intro s x
  change (ContactRelativeInfinityJet318.power S c (L' R S f c L) b).range.mkQ
    (ContactRelativeTwistKernel318.globalEquivalence S c (L' R S f c L) ((b+1 : ℕ) : ℤ)
      (zeroEquivalence R S f c L b hz (s ⊗ₜ[R] x))).val.2 =
    oneEquivalence R S f c L b (s ⊗ₜ[R] (ContactRelativeInfinityJet318.power R c L b).range.mkQ
      (ContactRelativeTwistKernel318.globalEquivalence R c L ((b+1 : ℕ) : ℤ) x).val.2)
  rw [one_pure]
  apply congrArg (ContactRelativeInfinityJet318.power S c (L' R S f c L) b).range.mkQ
  have he := congrArg Prod.snd (zero_coordinates R S f c L b hz s x)
  rw [ContactRelativeHZeroBaseChange318.pair_tmul] at he
  exact he
end ContactFiniteComplexCoefficient318
