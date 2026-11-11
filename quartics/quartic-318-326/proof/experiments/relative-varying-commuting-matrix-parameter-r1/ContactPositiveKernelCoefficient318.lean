module
public import ContactCoefficientCoordinatePowers318
public import ContactRelativeHZeroBaseChange318
public section
noncomputable section
namespace ContactPositiveKernelCoefficient318
open AlgebraicGeometry CategoryTheory LineSheafClass318 TensorProduct
open ContactOriginalRelativePolynomialCharts318 ContactOriginalRelativeLineOverlap318
open ContactOriginalCoefficientActions318 ContactCoefficientNativeSections318
open ContactRelativeGeometricTwist318
open scoped TensorProduct
set_option maxHeartbeats 850000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R S : CommRingCat.{0}) [Algebra ℚ R] [Algebra ℚ S]
  (f : R →ₐ[ℚ] S) (c : Fin 4 → ℚˣ) (L : Line (curve R c)) (d : ℤ)
local instance : Algebra R S := f.toAlgebra
local instance : Module R (finiteSections R c L) := finiteModule R c L
local instance : Module R (infinitySections R c L) := infinityModule R c L
local instance : Module R (originalSections R c L) := overlapModule R c L
local instance : Module S (finiteSections S c (L' R S f c L)) := finiteModule S c _
local instance : Module S (infinitySections S c (L' R S f c L)) := infinityModule S c _
local instance : Module S (originalSections S c (L' R S f c L)) := overlapModule S c _

/-- The actual coefficient square for the POSITIVE differential retains
both original chart restrictions and the actual Laurent monomial. -/
lemma square : (ContactRelativeTwistKernel318.positiveDifference S c (L' R S f c L) d).comp
    (ContactRelativeHZeroBaseChange318.pairEquivalence R S f c L).toLinearMap =
    (overlapEquivalence R S f c L).toLinearMap.comp
      ((ContactRelativeTwistKernel318.positiveDifference R c L d).baseChange S) := by
  apply AlgebraTensorModule.ext
  intro s x
  have h0 := LinearMap.congr_fun (ContactCoefficientCechBaseChange318.finite_square R S f c L) (s ⊗ₜ[R] x.1)
  have h1 := LinearMap.congr_fun (ContactCoefficientCechBaseChange318.infinity_square R S f c L) (s ⊗ₜ[R] x.2)
  have hv := LinearMap.congr_fun (ContactCoefficientCoordinatePowers318.overlap_square R S f c L d)
    (s ⊗ₜ[R] ContactOriginalRelativeOverlapSpan318.infinityMap R c L x.2)
  simp only [LinearMap.comp_apply,LinearMap.baseChange_tmul] at h0 h1 hv
  change ContactRelativeTwistKernel318.positiveDifference S c (L' R S f c L) d
    (ContactRelativeHZeroBaseChange318.pairEquivalence R S f c L (s ⊗ₜ[R] x)) =
      overlapEquivalence R S f c L (s ⊗ₜ[R] ContactRelativeTwistKernel318.positiveDifference R c L d x)
  rw [ContactRelativeHZeroBaseChange318.pair_tmul]
  change _-_ = overlapEquivalence R S f c L (s ⊗ₜ[R] (_-_))
  rw [tmul_sub,map_sub,h0,hv,h1]

variable (hz : ∀ x : NonreducedLineMayerVietoris318.H1 (twist R c L d),x=0)

private def splitting : ∃ s : originalSections R c L →ₗ[R]
    (finiteSections R c L × infinitySections R c L),
    (ContactRelativeTwistKernel318.positiveDifference R c L d).comp s=LinearMap.id := by
  letI := ContactRelativeCechProjective318.overlap R c L
  exact SplitKernelBaseChange318.exists_splitting R _ _
    (ContactRelativeTwistKernel318.positiveDifference R c L d)
    (ContactRelativeTwistKernel318.surjective R c L d hz)

/-- Arbitrary coefficient extension of the actual positive kernel.
Splitting is produced from actual twist vanishing and actual overlap
projectivity, never from an unproved tensor left-exactness assertion. -/
@[expose] def equivalence : S ⊗[R] LinearMap.ker (ContactRelativeTwistKernel318.positiveDifference R c L d) ≃ₗ[S]
    LinearMap.ker (ContactRelativeTwistKernel318.positiveDifference S c (L' R S f c L) d) :=
  (SplitKernelBaseChange318.equivalence R _ _ (ContactRelativeTwistKernel318.positiveDifference R c L d)
    (splitting R c L d hz).choose (splitting R c L d hz).choose_spec S).trans
    (KernelComparisonTransport318.equivalence _ _
      (ContactRelativeHZeroBaseChange318.pairEquivalence R S f c L)
      (overlapEquivalence R S f c L) (square R S f c L d))

lemma coordinates (s : S) (x : LinearMap.ker (ContactRelativeTwistKernel318.positiveDifference R c L d)) :
    (equivalence R S f c L d hz (s ⊗ₜ[R] x)).val=
      ContactRelativeHZeroBaseChange318.pairEquivalence R S f c L (s ⊗ₜ[R] x.val) := rfl
end ContactPositiveKernelCoefficient318
