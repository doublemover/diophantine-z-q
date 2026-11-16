module
public import PELOriginalLogMetricDerivatives318
public section
noncomputable section
namespace PELOriginalMetricCurvature318
open QuaternionicRealPeriod318 PELPeriodRiemannForm318 PELOriginalHermitianForm318
open PELOriginalLogMetricDerivatives318
variable (τ:ℂ) (hτ:0<τ.im)

/-- Real normalization of the curvature pairing of the actual log metric:
(D² log(h)(v,iw)-D² log(h)(w,iv))/(4π). The convention is explicit
so neither the sign nor a factor of 2π is hidden in a transported form. -/
@[expose] def curvature (z v w:ComplexVectors):ℝ:=
  (fderiv ℝ (fun y:ComplexVectors=>fderiv ℝ (logWeight τ hτ) y (Complex.I • w)) z v-
   fderiv ℝ (fun y:ComplexVectors=>fderiv ℝ (logWeight τ hτ) y (Complex.I • v)) z w)/
    (4*Real.pi)
lemma imaginary_twice (z:ComplexVectors):Complex.I • (Complex.I • z)=(-1:ℝ) • z:=by
  ext i
  simp [smul_smul]

/-- The ACTUAL second derivatives recover the SAME original integral
Riemann form. This is not a curvature form chosen after the fact. -/
theorem exact_original_form (z v w:ComplexVectors):curvature τ hτ z v w=riemann τ hτ v w:=by
  simp only [curvature,second_value,imaginary_twice,smul_right]
  rw [skew τ hτ w v]
  field_simp [Real.pi_ne_zero]
  ring
lemma independent_of_frame_lift (z z' v w:ComplexVectors):
    curvature τ hτ z v w=curvature τ hτ z' v w:=by
  rw [exact_original_form,exact_original_form]
lemma alternating (z v:ComplexVectors):curvature τ hτ z v v=0:=by
  rw [exact_original_form,PELPeriodRiemannForm318.alternating]
lemma positive (z v:ComplexVectors) (hv:v≠0):
    0<curvature τ hτ z v (Complex.I • v):=by
  rw [exact_original_form]
  exact PELPeriodRiemannForm318.positive τ hτ v hv
lemma original_integral (z:ComplexVectors)
    (l m:PELOriginalPeriodLattice318.lattice τ hτ):
    curvature τ hτ z l.val m.val=(integralRiemann τ hτ l m:ℝ):=by
  rw [exact_original_form]
  exact integralRiemann_value τ hτ l m

/-- Unimodularity is on the full original period lattice, not merely a
finite-index sublattice used for a choice of local coordinates. -/
theorem original_perfect
    (f:PELOriginalPeriodLattice318.lattice τ hτ→ₗ[ℤ]ℤ):
    ∃!l:PELOriginalPeriodLattice318.lattice τ hτ,
      ∀m,curvature τ hτ 0 l.val m.val=(f m:ℝ):=by
  obtain ⟨l,hl,hu⟩:=PELPeriodRiemannForm318.perfect τ hτ f
  refine ⟨l,?_,?_⟩
  · intro m
    rw [original_integral,hl]
  · intro k hk
    apply hu
    intro m
    have h:=hk m
    rw [original_integral] at h
    exact_mod_cast h
end PELOriginalMetricCurvature318
