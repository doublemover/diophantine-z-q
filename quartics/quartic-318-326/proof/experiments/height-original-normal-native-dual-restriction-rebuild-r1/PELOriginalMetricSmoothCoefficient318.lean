module
public import PELOriginalPolarizationMetric318
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public section
noncomputable section
namespace PELOriginalMetricSmoothCoefficient318
open QuaternionicRealPeriod318 PELPeriodRiemannForm318 PELOriginalPolarizationMetric318
variable (τ:ℂ) (hτ:0<τ.im)

/-- The actual Riemann form, as a continuous real bilinear map. Its
continuity is derived in the original finite-dimensional carrier. -/
@[expose] def secondLinear (z:ComplexVectors):ComplexVectors→ₗ[ℝ]ℝ where
  toFun:=riemann τ hτ z
  map_add':=add_right τ hτ z
  map_smul':=fun a w=>smul_right τ hτ a z w
@[expose] def bilinear:ComplexVectors→L[ℝ]ComplexVectors→L[ℝ]ℝ:=
  (show ComplexVectors→ₗ[ℝ]ComplexVectors→L[ℝ]ℝ from
    { toFun:=fun z=>(secondLinear τ hτ z).toContinuousLinearMap
      map_add':=by intro z w; ext v; exact add_left τ hτ z w v
      map_smul':=by intro a z; ext v; exact smul_left τ hτ a z v }).toContinuousLinearMap
lemma smooth_form:ContDiff ℝ ⊤ (fun p:ComplexVectors×ComplexVectors=>riemann τ hτ p.1 p.2):=
  (bilinear τ hτ).analyticOnNhd_bilinear Set.univ |>.contDiff
lemma smooth_weight:ContDiff ℝ ⊤ (weight τ hτ):=by
  have h:ContDiff ℝ ⊤ (fun z:ComplexVectors=>riemann τ hτ z (Complex.I • z)):=
    (smooth_form τ hτ).comp (contDiff_id.prodMk (contDiff_const.smul contDiff_id))
  exact Real.contDiff_exp.comp (contDiff_const.mul h)
lemma smooth_norm_square:ContDiff ℝ ⊤ (fun v:ℂ=>‖v‖^2):=by
  have h:ContDiff ℝ ⊤ (fun v:ℂ=>v.re*v.re+v.im*v.im):=
    (Complex.reCLM.contDiff.mul Complex.reCLM.contDiff).add
      (Complex.imCLM.contDiff.mul Complex.imCLM.contDiff)
  simpa only [Complex.sq_norm,Complex.normSq_apply] using h
lemma smooth_local_metric:ContDiff ℝ ⊤ (squaredNorm τ hτ):=
  (smooth_norm_square.comp contDiff_snd).mul ((smooth_weight τ hτ).comp contDiff_fst)
end PELOriginalMetricSmoothCoefficient318
