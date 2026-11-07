module
public import ImaginaryGradient318
public import Mathlib.Analysis.InnerProductSpace.Calculus
public section
noncomputable section
open Filter Set CompactMetricComparison318 ConformalCurvature318 FiniteLaplacian318
open InnerProductSpace HarmonicAxis318 ImaginaryGradient318
open scoped Topology
namespace HolomorphicPoincare318
set_option maxHeartbeats 0

/-- The actual Poincare pullback under a holomorphic local uniformizing map. -/
@[expose] def coefficient (f:ℂ→ℂ) (w:ℝ×ℝ) : ℝ :=
  ‖deriv f (coord w)‖^2/(f (coord w)).im^2

theorem laplacian_const_mul (a:ℝ) (f:ℝ×ℝ→ℝ) :
    laplacianAtOrigin (fun w=>a*f w)=a*laplacianAtOrigin f := by
  simp only [laplacianAtOrigin,deriv_const_mul_field',deriv_const_mul_field]
  ring

theorem im_axisC2 (f:ℂ→ℂ) (hf:AnalyticAt ℂ f 0) : AxisC2 (fun w=>(f (coord w)).im) :=
  axisC2 _ hf.harmonicAt_im.1

theorem coefficient_axisC2 (f:ℂ→ℂ) (hf:AnalyticAt ℂ f 0) (hupper:0<(f 0).im) :
    AxisC2 (coefficient f) := by
  have hdc:ContDiffAt ℝ 2 (deriv f) 0:=hf.deriv.contDiffAt.restrict_scalars ℝ
  have hn:ContDiffAt ℝ 2 (fun z:ℂ=>‖deriv f z‖^2) 0 :=
    hdc.norm_sq (𝕜:=ℂ)
  have hy:ContDiffAt ℝ 2 (fun z:ℂ=>(f z).im^2) 0:=hf.harmonicAt_im.1.pow 2
  exact axisC2 _ (hn.div hy (pow_ne_zero 2 hupper.ne'))

theorem coefficient_positive (f:ℂ→ℂ) (hupper:0<(f 0).im) (hderiv:deriv f 0≠0) :
    0<coefficient f (0,0) := by
  simp only [coefficient,coord,Complex.ofReal_zero,zero_mul,zero_add]
  exact div_pos (sq_pos_of_pos (norm_pos_iff.mpr hderiv)) (sq_pos_of_pos hupper)

theorem log_decomposition (f:ℂ→ℂ) (hf:AnalyticAt ℂ f 0)
    (hupper:0<(f 0).im) (hderiv:deriv f 0≠0) :
    (fun w=>Real.log (coefficient f w))=ᶠ[𝓝 (0,0)]
      (fun w=>2*Real.log ‖deriv f (coord w)‖-2*Real.log (f (coord w)).im) := by
  have hc:ContinuousAt coord (0,0) := by unfold coord;fun_prop
  have hd:ContinuousAt (fun w=>deriv f (coord w)) (0,0) := by
    have hh:ContinuousAt (deriv f) (coord (0,0)):=by simpa [coord] using hf.deriv.continuousAt
    exact hh.comp hc
  have hy:ContinuousAt (fun w=>(f (coord w)).im) (0,0) := by
    have hh:ContinuousAt (fun z:ℂ=>(f z).im) (coord (0,0)):=by simpa [coord] using hf.harmonicAt_im.1.continuousAt
    exact hh.comp hc
  have hd0:deriv f (coord (0,0))≠0:=by simpa [coord] using hderiv
  have hy0:(f (coord (0,0))).im≠0:=by simpa [coord] using hupper.ne'
  filter_upwards [hd.eventually_ne hd0,hy.eventually_ne hy0] with w hdw hyw
  rw [coefficient,Real.log_div (pow_ne_zero 2 (norm_ne_zero_iff.mpr hdw)) (pow_ne_zero 2 hyw),
    Real.log_pow,Real.log_pow]
  norm_num

/-- Actual local hyperbolic curvature in an arbitrary noncritical holomorphic
chart. Neither a harmonicity nor a Cauchy-Riemann gradient identity is assumed. -/
theorem curvature_eq_neg_one (f:ℂ→ℂ) (hf:AnalyticAt ℂ f 0)
    (hupper:0<(f 0).im) (hderiv:deriv f 0≠0) :
    curvature (coefficient f)=-1 := by
  have hlog:AxisC2 (fun w=>Real.log ‖deriv f (coord w)‖):=
    axisC2 _ (hf.deriv.harmonicAt_log_norm hderiv).1
  have him:AxisC2 (fun w=>Real.log (f (coord w)).im):=
    ⟨(im_axisC2 f hf).1.log (by simpa [coord] using hupper.ne'),
     (im_axisC2 f hf).2.log (by simpa [coord] using hupper.ne')⟩
  have hl0:=harmonic_laplacian _ (hf.deriv.harmonicAt_log_norm hderiv)
  have hi0:=harmonic_laplacian _ hf.harmonicAt_im
  have hi:laplacianAtOrigin (fun w=>Real.log (f (coord w)).im)=
      -‖deriv f 0‖^2/(f 0).im^2 := by
    rw [laplacian_log _ (im_axisC2 f hf) (by simpa [coord] using hupper.ne'),
      hi0,gradientSq_im f hf.differentiableAt]
    simp only [zero_mul,zero_sub,coord,Complex.ofReal_zero,zero_mul,zero_add]
  have hl:laplacianAtOrigin (fun w=>Real.log (coefficient f w))=
      2*‖deriv f 0‖^2/(f 0).im^2 := by
    rw [laplacian_congr (log_decomposition f hf hupper hderiv),
      laplacian_sub _ _ ⟨contDiffAt_const.mul hlog.1,contDiffAt_const.mul hlog.2⟩
        ⟨contDiffAt_const.mul him.1,contDiffAt_const.mul him.2⟩,
      laplacian_const_mul,laplacian_const_mul,hl0,hi]
    ring
  rw [curvature,hl,coefficient]
  simp only [coord,Complex.ofReal_zero,zero_mul,zero_add]
  have hn:‖deriv f 0‖≠0:=norm_ne_zero_iff.mpr hderiv
  field_simp

end HolomorphicPoincare318
#print axioms HolomorphicPoincare318.curvature_eq_neg_one
