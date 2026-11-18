module
public import AnalyticBoundaryOrderOne318
public section
noncomputable section
namespace AnalyticDiskBoundaryNoncritical318
open Complex Set Filter
open scoped Topology ComplexConjugate
set_option maxHeartbeats 2800000

@[expose] def cayley (w : ℂ) : ℂ := I*(1-w)/(1+w)

lemma cayley_im (w : ℂ) : (cayley w).im=(1-normSq w)/normSq (1+w) := by
  simp only [cayley,Complex.div_im,Complex.mul_re,Complex.mul_im,
    Complex.sub_re,Complex.sub_im,Complex.add_re,Complex.add_im,
    Complex.one_re,Complex.one_im,Complex.I_re,Complex.I_im,Complex.normSq_apply]
  ring

lemma cayley_analytic_one : AnalyticAt ℂ cayley 1 := by
  unfold cayley
  fun_prop (disch := norm_num)

lemma cayley_unit (w : ℂ) (hw : ‖w‖=1) : (cayley w).im=0 := by
  rw [cayley_im,Complex.normSq_eq_norm_sq,hw]
  norm_num

lemma cayley_disk (w : ℂ) (hw : ‖w‖<1) : 0<(cayley w).im := by
  have hn : normSq w<1 := by
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [norm_nonneg w]
  have hd : 1+w≠0 := by
    intro he
    have he' : w= -1 := by linear_combination he
    rw [he'] at hw
    norm_num at hw
  rw [cayley_im]
  exact div_pos (sub_pos.mpr hn) (Complex.normSq_pos.mpr hd)

/-- An actual analytic disk-boundary extension is noncritical on the
open seam. The circle trace and strict interior disk inequality are the
ONLY geometric inputs; no boundary injectivity, nonzero derivative or
Caratheodory homeomorphism is assumed. -/
theorem derivative_ne_zero {f : ℂ → ℂ} (hf : AnalyticAt ℂ f 0)
    (hf0 : ‖f 0‖=1)
    (hr : ∀ᶠ z in 𝓝 (0:ℂ),z.im=0 → ‖f z‖=1)
    (hu : ∀ᶠ z in 𝓝 (0:ℂ),0<z.im → ‖f z‖<1) : deriv f 0≠0 := by
  let F : ℂ → ℂ := fun z => conj (f 0)*f z
  have hFa : AnalyticAt ℂ F 0 := analyticAt_const.mul hf
  have hF0 : F 0=1 := by
    change conj (f 0)*f 0=1
    rw [mul_comm,Complex.mul_conj,Complex.normSq_eq_norm_sq,hf0]
    norm_num
  have hFnorm (z : ℂ) : ‖F z‖=‖f z‖ := by
    simp only [F,norm_mul,Complex.norm_conj,hf0,one_mul]
  let H : ℂ → ℂ := fun z => cayley (F z)
  have hca : AnalyticAt ℂ cayley (F 0) := by rw [hF0]; exact cayley_analytic_one
  have hHa : AnalyticAt ℂ H 0 := hca.comp hFa
  have hH0 : H 0=0 := by simp only [H,hF0,cayley,sub_self,mul_zero,zero_div]
  have hHr : ∀ᶠ z in 𝓝 (0:ℂ),z.im=0 → (H z).im=0 := by
    filter_upwards [hr] with z hz hzi
    exact cayley_unit (F z) (by rw [hFnorm]; exact hz hzi)
  have hHu : ∀ᶠ z in 𝓝 (0:ℂ),0<z.im → 0<(H z).im := by
    filter_upwards [hu] with z hz hzi
    exact cayley_disk (F z) (by rw [hFnorm]; exact hz hzi)
  have hdH := (AnalyticBoundaryOrderOne318.order_one hHa hH0 hHr hHu).2
  have hFd : HasDerivAt F (conj (f 0)*deriv f 0) 0 :=
    hf.differentiableAt.hasDerivAt.const_mul _
  have hHd := hca.differentiableAt.hasDerivAt.comp 0 hFd
  intro hd
  apply hdH
  have hh : deriv H 0=deriv cayley (F 0)*(conj (f 0)*deriv f 0) := hHd.deriv
  simpa only [hd,mul_zero] using hh
end AnalyticDiskBoundaryNoncritical318
