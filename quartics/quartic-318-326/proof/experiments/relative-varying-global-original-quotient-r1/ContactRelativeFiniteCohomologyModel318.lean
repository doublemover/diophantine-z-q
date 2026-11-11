module
public import ContactRelativeTwistKernel318
public import ContactRelativeInfinityJet318
public import ContactRelativeGeometricVanishing318
public import TwoChartJetCokernel318
public section
noncomputable section
namespace ContactRelativeFiniteCohomologyModel318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open ContactOriginalRelativePolynomialCharts318 ContactOriginalRelativeLineOverlap318
open ContactOriginalCoefficientActions318 ContactRelativeGeometricTwist318
open ContactOriginalRelativeOverlapSpan318
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ) (L : Line (curve R c)) (b : ℕ)
local instance : Module R (finiteSections R c L) := finiteModule R c L
local instance : Module R (infinitySections R c L) := infinityModule R c L
local instance : Module R (originalSections R c L) := overlapModule R c L
local instance : Module (LaurentPolynomial R) (originalSections R c L) := overlapLaurentModule R c L
local instance (N : Line (curve R c)) : Module R Γ(N.object,⊤) :=
  OriginalCoefficientCohomology318.sectionModule R (ContactRelativeStructuralHOne318.projection R c) N ⊤
local instance : Module R (NonreducedLineMayerVietoris318.H1 L) :=
  OriginalCoefficientCohomology318.cohomologyModule R (ContactRelativeStructuralHOne318.projection R c) L 1

lemma original_power (x : infinitySections R c L) :
    ContactRelativeTwistKernel318.shift R c L ((b+1 : ℕ) : ℤ)
      (infinityMap R c L (ContactRelativeInfinityJet318.power R c L b x)) = infinityMap R c L x := by
  have hx := infinity_polynomial R c L (Polynomial.X ^ (b+1)) x
  rw [Polynomial.toLaurent_X_pow,LaurentPolynomial.invert_T] at hx
  change infinityMap R c L (ContactRelativeInfinityJet318.power R c L b x) =
    (LaurentPolynomial.T (-((b+1 : ℕ) : ℤ)) : LaurentPolynomial R) • infinityMap R c L x at hx
  change (LaurentPolynomial.T ((b+1 : ℕ) : ℤ) : LaurentPolynomial R) •
    infinityMap R c L (ContactRelativeInfinityJet318.power R c L b x) = _
  rw [hx,smul_smul,← LaurentPolynomial.T_add,add_neg_cancel,LaurentPolynomial.T_zero,one_smul]

/-- Genuine finite-complex first term: sections of the ACTUAL positive
geometric twist, with the independently structural R action. -/
abbrev termZero := Γ((twist R c L ((b+1 : ℕ) : ℤ)).object,⊤)
/-- Genuine second term: jets of the ORIGINAL infinity line module. -/
abbrev termOne := infinitySections R c L ⧸ (ContactRelativeInfinityJet318.power R c L b).range

@[expose] def differential : termZero R c L b →ₗ[R] termOne R c L b :=
  (TwoChartJetDifferential318.jet (finiteMap R c L) (infinityMap R c L)
    (ContactRelativeInfinityJet318.power R c L b)
    (ContactRelativeTwistKernel318.shift R c L ((b+1 : ℕ) : ℤ))).comp
    (ContactRelativeTwistKernel318.globalEquivalence R c L ((b+1 : ℕ) : ℤ)).toLinearMap

lemma differential_range : (differential R c L b).range =
    (TwoChartJetDifferential318.jet (finiteMap R c L) (infinityMap R c L)
      (ContactRelativeInfinityJet318.power R c L b)
      (ContactRelativeTwistKernel318.shift R c L ((b+1 : ℕ) : ℤ))).range := by
  ext q
  constructor
  · rintro ⟨x,rfl⟩
    exact ⟨ContactRelativeTwistKernel318.globalEquivalence R c L ((b+1 : ℕ) : ℤ) x,rfl⟩
  · rintro ⟨x,rfl⟩
    refine ⟨(ContactRelativeTwistKernel318.globalEquivalence R c L ((b+1 : ℕ) : ℤ)).symm x,?_⟩
    change _ ((ContactRelativeTwistKernel318.globalEquivalence R c L _)
      ((ContactRelativeTwistKernel318.globalEquivalence R c L _).symm x))=_
    rw [LinearEquiv.apply_symm_apply]

/-- Degree zero is the SAME original global line sections. Its comparison
retains the original (a,b)↦(a,u^(b+1)b) inclusion into the positive twist. -/
@[expose] def hzero : Γ(L.object,⊤) ≃ₗ[R] LinearMap.ker (differential R c L b) :=
  (ContactRelativeOriginalHZero318.equivalence R c L).trans
    ((TwoChartJetDifferential318.kernelEquivalence (finiteMap R c L) (infinityMap R c L)
      (ContactRelativeInfinityJet318.power R c L b)
      (ContactRelativeTwistKernel318.shift R c L ((b+1 : ℕ) : ℤ))
      (original_power R c L b) (ContactRelativeInfinityJet318.injective R c L b)).trans
      (KernelComparisonTransport318.equivalence (differential R c L b)
        (TwoChartJetDifferential318.jet (finiteMap R c L) (infinityMap R c L)
          (ContactRelativeInfinityJet318.power R c L b)
          (ContactRelativeTwistKernel318.shift R c L ((b+1 : ℕ) : ℤ)))
        (ContactRelativeTwistKernel318.globalEquivalence R c L ((b+1 : ℕ) : ℤ))
        (LinearEquiv.refl R _) (by rfl)).symm)

/-- Degree one is the independently structural ACTUAL derived H1, via
its original boundary, with the true infinity-jet connecting map. -/
@[expose] def hone
    (hz : ∀ x : NonreducedLineMayerVietoris318.H1 (twist R c L ((b+1 : ℕ) : ℤ)),x=0) :
    (termOne R c L b ⧸ (differential R c L b).range) ≃ₗ[R] NonreducedLineMayerVietoris318.H1 L :=
  (Submodule.quotEquivOfEq _ _ (differential_range R c L b)).trans
    ((TwoChartJetCokernel318.equivalence (finiteMap R c L) (infinityMap R c L)
      (ContactRelativeInfinityJet318.power R c L b)
      (ContactRelativeTwistKernel318.shift R c L ((b+1 : ℕ) : ℤ))
      (original_power R c L b) (ContactRelativeTwistKernel318.surjective R c L _ hz)).trans
      ((Submodule.quotEquivOfEq _ _ (ContactRelativeCechProjective318.range_difference R c L)).trans
        (ContactRelativeStructuralHOne318.equivalence R c L)))

/-- The actual two-term linear complex has finite projective terms when
the actual positive twist has zero H1. No finiteness of its H0 kernel
for arbitrary original L is inferred over a noncoherent coefficient ring. -/
theorem finite_projective
    (hz : ∀ x : NonreducedLineMayerVietoris318.H1 (twist R c L ((b+1 : ℕ) : ℤ)),x=0) :
    (Module.Finite R (termZero R c L b) ∧ Module.Projective R (termZero R c L b)) ∧
    (Module.Finite R (termOne R c L b) ∧ Module.Projective R (termOne R c L b)) :=
  ⟨ContactRelativeFiniteProjectiveHZero318.finite_projective R c _ hz,
    ContactRelativeInfinityJet318.finite_projective R c L b⟩

/-- Every actual line over every affine coefficient test admits this
concrete finite-projective two-term model of its original H0 and H1. The
positive integer is produced internally from genuine twist vanishing. -/
theorem exists_model : ∃ b : ℕ,
    (∀ x : NonreducedLineMayerVietoris318.H1 (twist R c L ((b+1 : ℕ) : ℤ)),x=0) ∧
    (Module.Finite R (termZero R c L b) ∧ Module.Projective R (termZero R c L b)) ∧
    (Module.Finite R (termOne R c L b) ∧ Module.Projective R (termOne R c L b)) := by
  obtain ⟨N,hN⟩ := ContactRelativeGeometricVanishing318.exists_bound R c L
  have hz := hN (N+1) (Nat.le_succ N)
  exact ⟨N,hz,finite_projective R c L N hz⟩
end ContactRelativeFiniteCohomologyModel318
