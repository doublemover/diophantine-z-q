module
public import ThreeJQuotientDerivation318
public import Mathlib.RingTheory.Ideal.Operations
public section
noncomputable section
namespace ThreeJRelativeDifferentials318
open Polynomial ThreeJMonicAlgebra318 ThreeJQuotientDerivation318
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

abbrev Omega := KaehlerDifferential Base Model
@[expose] def dt : Omega := KaehlerDifferential.D Base Model t
@[expose] def generator : Model →ₗ[Model] Omega := LinearMap.toSpanSingleton Model Omega dt
lemma generator_apply (a : Model) : generator a=a • dt := rfl

/-- Differentiating the original monic equation gives the exact relation
for the relative differential of its original parameter. -/
lemma derivative_relation : delta • dt=0 := by
  have h := (KaehlerDifferential.D Base Model).map_aeval polynomial t
  change KaehlerDifferential.D Base Model (evaluation polynomial)=delta • dt at h
  rw [evaluation_polynomial,map_zero] at h
  exact h.symm

lemma generator_surjective : Function.Surjective generator := by
  rw [←LinearMap.range_eq_top]
  apply top_unique
  rw [←KaehlerDifferential.span_range_derivation Base Model,Submodule.span_le]
  rintro _ ⟨a,rfl⟩
  obtain ⟨q,rfl⟩ := evaluation_surjective a
  refine ⟨evaluation q.derivative,?_⟩
  exact ((KaehlerDifferential.D Base Model).map_aeval q t).symm

/-- The actual quotient-valued derivation induces a detector on Omega.
This supplies the converse to the differentiated polynomial relation. -/
@[expose] def detector : Omega →ₗ[Model] DifferentialQuotient :=
  quotientDerivation.liftKaehlerDifferential
lemma detector_dt : detector dt=1 := by
  exact (Derivation.liftKaehlerDifferential_comp_D quotientDerivation t).trans quotientDerivation_t
lemma detector_generator (a : Model) : detector (generator a)=quotientMap a := by
  rw [generator_apply,map_smul,detector_dt,Algebra.smul_def,mul_one]
  rfl

/-- Exact kernel, not only an annihilating polynomial: there are no extra
relations in the cyclic relative differential module. -/
theorem generator_kernel : LinearMap.ker generator=(derivativeIdeal : Submodule Model Model) := by
  apply le_antisymm
  · intro a ha
    have h := congrArg detector (LinearMap.mem_ker.mp ha)
    rw [detector_generator,map_zero] at h
    exact Ideal.Quotient.eq_zero_iff_mem.mp h
  · change Ideal.span {delta} ≤ LinearMap.ker generator
    rw [Ideal.span_le]
    intro a ha
    rcases Set.mem_singleton_iff.mp ha with rfl
    exact derivative_relation

/-- A full relative differential-module presentation for the exact original
quartic j-algebra, proved by two-sided universal-property arguments. -/
@[expose] def differentialEquiv : DifferentialQuotient ≃ₗ[Model] Omega := by
  change (Model ⧸ (derivativeIdeal : Submodule Model Model)) ≃ₗ[Model] Omega
  rw [←generator_kernel]
  exact generator.quotKerEquivOfSurjective generator_surjective

/-- The same exact kernel statement expressed in the original Laurent
coordinate, retaining the factor S and the original elliptic polynomial. -/
theorem original_coordinate_relation :
    ThreeJLaurentEquiv318.coordinateEquiv delta=
      ProjectiveLineOverlap318.s*(ProjectiveLineOverlap318.t+243)^2*
        ThreeJDerivativeOpen318.ellipticFactor := by
  change ThreeJLaurentEquiv318.coordinateEquiv
    (evaluation polynomial.derivative)=_
  rw [evaluation_mk]
  exact ThreeJDerivativeOpen318.derivative_factorization

/-- The exact annihilator ideal transported into the original Laurent
chart, rather than the reduced set of its complex zeros. -/
@[expose] def originalDifferentialIdeal : Ideal ThreeJLaurentEquiv318.Laurent :=
  Ideal.map ThreeJLaurentEquiv318.coordinateEquiv.toRingHom derivativeIdeal

lemma original_ideal_generator : originalDifferentialIdeal=
    Ideal.span {ThreeJDerivativeOpen318.derivativeImage} := by
  have h : ThreeJLaurentEquiv318.coordinateEquiv delta=ThreeJDerivativeOpen318.derivativeImage := by
    change ThreeJLaurentEquiv318.coordinateEquiv
      (evaluation polynomial.derivative)=ThreeJDerivativeOpen318.derivativeImage
    rw [evaluation_mk]
    rfl
  rw [originalDifferentialIdeal,derivativeIdeal,Ideal.map_span,Set.image_singleton]
  exact congrArg (fun a => Ideal.span {a}) h

lemma remove_laurent_unit :
    Ideal.span {ThreeJDerivativeOpen318.derivativeImage}=
    Ideal.span {(ProjectiveLineOverlap318.t+243)^2*ThreeJDerivativeOpen318.ellipticFactor} := by
  apply le_antisymm
  · rw [Ideal.span_singleton_le_iff_mem,Ideal.mem_span_singleton]
    refine ⟨ProjectiveLineOverlap318.s,?_⟩
    rw [ThreeJDerivativeOpen318.derivative_factorization]
    ring
  · rw [Ideal.span_singleton_le_iff_mem,Ideal.mem_span_singleton]
    refine ⟨ProjectiveLineOverlap318.t,?_⟩
    exact (ThreeJDerivativeOpen318.derivative_times_parameter).symm.trans (mul_comm _ _)

/-- Scheme-theoretic multiplicities on the entire Laurent chart: the
relative differential ideal has the squared -243 factor and one copy of
the original elliptic quadratic. This does not assert a global Cartier
divisor extension over the two omitted source points. -/
theorem original_differential_ideal_factorization : originalDifferentialIdeal=
    (Ideal.span {ProjectiveLineOverlap318.t+243})^2*
      Ideal.span {ThreeJDerivativeOpen318.ellipticFactor} := by
  rw [original_ideal_generator,remove_laurent_unit,Ideal.span_singleton_pow,
    Ideal.span_singleton_mul_span_singleton]

theorem annihilates_iff (a : Model) : (∀ w : Omega, a • w=0) ↔ a ∈ derivativeIdeal := by
  constructor
  · intro h
    have hg : a ∈ LinearMap.ker generator := h dt
    rw [generator_kernel] at hg
    exact hg
  · intro h w
    obtain ⟨b,rfl⟩ := generator_surjective w
    have ha : generator a=0 := by
      apply LinearMap.mem_ker.mp
      rw [generator_kernel]
      exact h
    change a • (b • dt)=0
    rw [smul_comm]
    change b • generator a=0
    rw [ha,smul_zero]

end ThreeJRelativeDifferentials318
