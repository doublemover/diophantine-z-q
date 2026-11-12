module
public import ContactRelativeFiniteCohomologyModel318
public import TwoChartJetChainMap318
public section
noncomputable section
namespace ContactRelativeFiniteCechComparison318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open ContactOriginalRelativePolynomialCharts318 ContactOriginalRelativeLineOverlap318
open ContactOriginalCoefficientActions318 ContactRelativeGeometricTwist318
open ContactOriginalRelativeOverlapSpan318 ContactRelativeFiniteCohomologyModel318
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ) (L : Line (curve R c)) (b : ℕ)
local instance : Module R (finiteSections R c L) := finiteModule R c L
local instance : Module R (infinitySections R c L) := infinityModule R c L
local instance : Module R (originalSections R c L) := overlapModule R c L
local instance (N : Line (curve R c)) : Module R Γ(N.object,⊤) :=
  OriginalCoefficientCohomology318.sectionModule R (ContactRelativeStructuralHOne318.projection R c) N ⊤

private def lifting : ∃ s : termOne R c L b →ₗ[R] infinitySections R c L,
    (ContactRelativeInfinityJet318.power R c L b).range.mkQ.comp s=LinearMap.id := by
  letI := (ContactRelativeInfinityJet318.finite_projective R c L b).2
  exact TwoChartJetChainMap318.exists_lift (ContactRelativeInfinityJet318.power R c L b)

@[expose] def jetLift : termOne R c L b →ₗ[R] infinitySections R c L := (lifting R c L b).choose
lemma jetLift_spec : (ContactRelativeInfinityJet318.power R c L b).range.mkQ.comp (jetLift R c L b)=LinearMap.id :=
  (lifting R c L b).choose_spec

/-- Actual degree-zero chain map into the original full-chart sections;
its second coordinate divides the literal jet-free residual by u^(b+1). -/
@[expose] def degreeZero : termZero R c L b →ₗ[R]
    finiteSections R c L × infinitySections R c L :=
  (TwoChartJetChainMap318.degreeZero (finiteMap R c L) (infinityMap R c L)
    (ContactRelativeInfinityJet318.power R c L b)
    (ContactRelativeTwistKernel318.shift R c L ((b+1 : ℕ) : ℤ))
    (ContactRelativeInfinityJet318.injective R c L b) (jetLift R c L b) (jetLift_spec R c L b)).comp
    (ContactRelativeTwistKernel318.globalEquivalence R c L ((b+1 : ℕ) : ℤ)).toLinearMap

/-- Actual degree-one chain map into the SAME original Laurent overlap. -/
@[expose] def degreeOne : termOne R c L b →ₗ[R] originalSections R c L :=
  TwoChartJetChainMap318.degreeOne (infinityMap R c L) (ContactRelativeInfinityJet318.power R c L b)
    (ContactRelativeTwistKernel318.shift R c L ((b+1 : ℕ) : ℤ)) (jetLift R c L b)

lemma square : (ContactRelativeCechProjective318.difference R c L).comp (degreeZero R c L b) =
    (degreeOne R c L b).comp (differential R c L b) := by
  ext x
  exact LinearMap.congr_fun (TwoChartJetChainMap318.square (finiteMap R c L) (infinityMap R c L)
    (ContactRelativeInfinityJet318.power R c L b)
    (ContactRelativeTwistKernel318.shift R c L ((b+1 : ℕ) : ℤ))
    (original_power R c L b) (ContactRelativeInfinityJet318.injective R c L b)
    (jetLift R c L b) (jetLift_spec R c L b))
    (ContactRelativeTwistKernel318.globalEquivalence R c L ((b+1 : ℕ) : ℤ) x)

/-- The induced H0 comparison is computed from this literal chain map. -/
@[expose] def onKernel : LinearMap.ker (differential R c L b) →ₗ[R]
    LinearMap.ker (ContactRelativeCechProjective318.difference R c L) :=
  (TwoChartJetChainMap318.onKernel (finiteMap R c L) (infinityMap R c L)
    (ContactRelativeInfinityJet318.power R c L b)
    (ContactRelativeTwistKernel318.shift R c L ((b+1 : ℕ) : ℤ))
    (original_power R c L b) (ContactRelativeInfinityJet318.injective R c L b)
    (jetLift R c L b) (jetLift_spec R c L b)).comp
    (KernelComparisonTransport318.equivalence (differential R c L b)
      (TwoChartJetDifferential318.jet (finiteMap R c L) (infinityMap R c L)
        (ContactRelativeInfinityJet318.power R c L b)
        (ContactRelativeTwistKernel318.shift R c L ((b+1 : ℕ) : ℤ)))
      (ContactRelativeTwistKernel318.globalEquivalence R c L ((b+1 : ℕ) : ℤ))
      (LinearEquiv.refl R _) (by rfl)).toLinearMap

lemma kernel_value (x : LinearMap.ker (differential R c L b)) :
    (onKernel R c L b x).val=degreeZero R c L b x := rfl

lemma onKernel_bijective : Function.Bijective (onKernel R c L b) :=
  (TwoChartJetChainMap318.onKernel_bijective (finiteMap R c L) (infinityMap R c L)
    (ContactRelativeInfinityJet318.power R c L b)
    (ContactRelativeTwistKernel318.shift R c L ((b+1 : ℕ) : ℤ))
    (original_power R c L b) (ContactRelativeInfinityJet318.injective R c L b)
    (jetLift R c L b) (jetLift_spec R c L b)).comp
    (KernelComparisonTransport318.equivalence (differential R c L b)
      (TwoChartJetDifferential318.jet (finiteMap R c L) (infinityMap R c L)
        (ContactRelativeInfinityJet318.power R c L b)
        (ContactRelativeTwistKernel318.shift R c L ((b+1 : ℕ) : ℤ)))
      (ContactRelativeTwistKernel318.globalEquivalence R c L ((b+1 : ℕ) : ℤ))
      (LinearEquiv.refl R _) (by rfl)).bijective

/-- The induced H1 map is the original jet connecting map, not an
unrelated equivalence between finite presentations. -/
@[expose] def onCokernel : (termOne R c L b ⧸ (differential R c L b).range) →ₗ[R]
    originalSections R c L ⧸ (ContactRelativeCechProjective318.difference R c L).range :=
  (TwoChartJetChainMap318.onCokernel (finiteMap R c L) (infinityMap R c L)
    (ContactRelativeInfinityJet318.power R c L b)
    (ContactRelativeTwistKernel318.shift R c L ((b+1 : ℕ) : ℤ))
    (original_power R c L b) (ContactRelativeInfinityJet318.injective R c L b)
    (jetLift R c L b) (jetLift_spec R c L b)).comp
    (Submodule.quotEquivOfEq _ _ (differential_range R c L b)).toLinearMap

lemma cokernel_value (q : termOne R c L b) :
    onCokernel R c L b ((differential R c L b).range.mkQ q)=
      (ContactRelativeCechProjective318.difference R c L).range.mkQ (degreeOne R c L b q) := rfl

lemma onCokernel_bijective
    (hz : ∀ x : NonreducedLineMayerVietoris318.H1 (twist R c L ((b+1 : ℕ) : ℤ)),x=0) :
    Function.Bijective (onCokernel R c L b) :=
  (TwoChartJetChainMap318.onCokernel_bijective (finiteMap R c L) (infinityMap R c L)
    (ContactRelativeInfinityJet318.power R c L b)
    (ContactRelativeTwistKernel318.shift R c L ((b+1 : ℕ) : ℤ))
    (original_power R c L b) (ContactRelativeInfinityJet318.injective R c L b)
    (jetLift R c L b) (jetLift_spec R c L b)
    (ContactRelativeTwistKernel318.surjective R c L _ hz)).comp
    (Submodule.quotEquivOfEq _ _ (differential_range R c L b)).bijective
end ContactRelativeFiniteCechComparison318
