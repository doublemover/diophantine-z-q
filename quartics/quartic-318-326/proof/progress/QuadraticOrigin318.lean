module
public import LiteralCurvature318
public section
noncomputable section
open Filter Set Finset CompactMetricComparison318 ConformalCurvature318
open scoped Topology ContDiff
namespace QuadraticOrigin318
set_option maxHeartbeats 0

theorem quadratic_deriv {f:ℝ→ℝ} (a:ℝ) (hf:ContDiffAt ℝ 2 f 0) :
    deriv (fun t:ℝ=>f (a*t^2)) 0=0 := by
  have hg:HasDerivAt (fun t:ℝ=>a*t^2) 0 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).pow 2).const_mul a
  have hfd:HasDerivAt f (deriv f 0) (a*0^2) := by simpa using (hf.differentiableAt (by norm_num)).hasDerivAt
  have hd:= hfd.comp 0 hg
  change HasDerivAt (fun t:ℝ=>f (a*t^2)) _ _ at hd
  simpa only [mul_zero] using hd.deriv

theorem quadratic_second_deriv {f:ℝ→ℝ} (a:ℝ) (hf:ContDiffAt ℝ 2 f 0) :
    deriv (deriv (fun t:ℝ=>f (a*t^2))) 0=2*a*deriv f 0 := by
  have ht:ContinuousAt (fun t:ℝ=>a*t^2) 0 := by fun_prop
  have hevent:∀ᶠ t:ℝ in 𝓝 0,ContDiffAt ℝ 2 f (a*t^2) := by
    have he := ht.tendsto.eventually (show ∀ᶠ s in 𝓝 (a*0^2), ContDiffAt ℝ 2 f s by simpa using hf.eventually (by norm_num))
    simpa using he
  have he:deriv (fun t:ℝ=>f (a*t^2))=ᶠ[𝓝 0]
      (fun t=>deriv f (a*t^2)*(a*(2*t))) := by
    filter_upwards [hevent] with t ht
    have hg:HasDerivAt (fun t:ℝ=>a*t^2) (a*(2*t)) t := by
      simpa using ((hasDerivAt_id t).pow 2).const_mul a
    exact ((ht.differentiableAt (by norm_num)).hasDerivAt.comp t hg).deriv
  rw [he.deriv_eq]
  have hg:HasDerivAt (fun t:ℝ=>a*t^2) 0 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).pow 2).const_mul a
  have hf':DifferentiableAt ℝ (deriv f) 0:=
    (hf.derivWithin (m:=1) (by norm_num)).differentiableAt (by norm_num)
  have hfd:HasDerivAt (deriv f) (deriv (deriv f) 0) (a*0^2) := by simpa using hf'.hasDerivAt
  have hcomp:=hfd.comp 0 hg
  have hlinear:HasDerivAt (fun t:ℝ=>a*(2*t)) (a*2) 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).const_mul 2).const_mul a
  have hd:=hcomp.mul hlinear
  change HasDerivAt (fun t:ℝ=>deriv f (a*t^2)*(a*(2*t))) _ _ at hd
  rw [hd.deriv]
  simp only [Function.comp_def,mul_zero,zero_mul,zero_add,zero_pow (by decide:2≠0)]
  ring

@[expose] def complexCoord (w:ℝ×ℝ) : ℂ := (w.1:ℂ)+w.2*Complex.I
@[expose] def quadraticDistance (b c:ℂ) (w:ℝ×ℝ) : ℝ := ‖b+c*(complexCoord w)^2‖

theorem line_smooth (b c:ℂ) (hb:b≠0) :
    ContDiffAt ℝ 2 (fun s:ℝ=>‖b+c*(s:ℂ)‖) 0 := by
  apply ContDiffAt.norm (𝕜:=ℂ)
  · exact contDiffAt_const.add (contDiffAt_const.mul Complex.ofRealCLM.contDiff.contDiffAt)
  · simpa using hb

theorem quadratic_axisC2 (b c:ℂ) (hb:b≠0) : AxisC2 (quadraticDistance b c) := by
  have hc:ContDiffAt ℝ ∞ (fun z:ℂ=>‖b+c*z^2‖) 0 := by
    apply ContDiffAt.norm (𝕜:=ℂ)
    · fun_prop
    · simpa using hb
  exact LiteralMetricExtension318.smooth_axisC2 (fun z:ℂ=>‖b+c*z^2‖) hc

theorem quadratic_x (b c:ℂ) :
    (fun t:ℝ=>quadraticDistance b c (t,0))=(fun t=>‖b+c*((t^2:ℝ):ℂ)‖) := by
  funext t
  simp [quadraticDistance,complexCoord]

theorem quadratic_y (b c:ℂ) :
    (fun t:ℝ=>quadraticDistance b c (0,t))=(fun t=>‖b+c*((-t^2:ℝ):ℂ)‖) := by
  funext t
  simp [quadraticDistance,complexCoord,mul_pow]

theorem quadratic_gradient (b c:ℂ) (hb:b≠0) :
    deriv (fun t=>quadraticDistance b c (t,0)) 0=0 ∧
    deriv (fun t=>quadraticDistance b c (0,t)) 0=0 := by
  rw [quadratic_x,quadratic_y]
  constructor
  · simpa using quadratic_deriv 1 (line_smooth b c hb)
  · simpa using quadratic_deriv (-1) (line_smooth b c hb)

theorem quadratic_laplacian (b c:ℂ) (hb:b≠0) :
    laplacianAtOrigin (quadraticDistance b c)=0 := by
  unfold laplacianAtOrigin
  rw [quadratic_x,quadratic_y]
  have hx:=quadratic_second_deriv 1 (line_smooth b c hb)
  have hy:=quadratic_second_deriv (-1) (line_smooth b c hb)
  simp only [one_mul,neg_mul,neg_pow,one_pow] at hx hy
  rw [hx,hy]
  ring
end QuadraticOrigin318
#print axioms QuadraticOrigin318.quadratic_laplacian
