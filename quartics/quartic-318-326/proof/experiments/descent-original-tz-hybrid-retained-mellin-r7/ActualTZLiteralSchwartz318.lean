module
public import ActualTZMellinKernel318
import all Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public section
noncomputable section
namespace ActualTZLiteralSchwartz318
open MeasureTheory Set
open scoped FourierTransform SchwartzMap ContDiff Topology
open ActualTZMellinKernel318

/-- The actual real smooth cutoff of the ordinary divisor sieve. Only
the support and smoothness are needed for Fourier inversion. -/
structure Cutoff where
  χ : ℝ → ℝ
  smooth : ContDiff ℝ ∞ χ
  support : ∀ t,1< |t|→χ t=0

@[expose] def scale : ℝ := 2*Real.pi

theorem scale_pos : 0<scale := by
  unfold scale
  positivity

@[expose] def tilt (C : Cutoff) (u : ℝ) : ℂ :=
  (Real.exp u:ℂ)*(C.χ u:ℂ)

private theorem tilt_smooth (C : Cutoff) : ContDiff ℝ ∞ (tilt C) := by
  exact (Complex.ofRealCLM.contDiff.comp Real.contDiff_exp).mul
    (Complex.ofRealCLM.contDiff.comp C.smooth)

private theorem tilt_support (C : Cutoff) : HasCompactSupport (tilt C) := by
  have h : Function.support (tilt C) ⊆ Set.Icc (-1:ℝ) 1 := by
    intro u hu
    by_contra hn
    have hab : 1< |u| := by
      by_contra hn'
      apply hn
      exact ⟨(abs_le.mp (le_of_not_gt hn')).1,(abs_le.mp (le_of_not_gt hn')).2⟩
    exact hu (by simp [tilt,C.support u hab])
  change IsCompact (closure (Function.support (tilt C)))
  exact isCompact_Icc.of_isClosed_subset isClosed_closure (closure_minimal h isClosed_Icc)

def tiltMap (C : Cutoff) : 𝓢(ℝ,ℂ) :=
  (tilt_support C).toSchwartzMap (tilt_smooth C)

private theorem tiltMap_apply_internal (C : Cutoff) (u : ℝ) : tiltMap C u=tilt C u := by
  unfold tiltMap <;> rfl

@[simp] theorem tiltMap_apply (C : Cutoff) (u : ℝ) : tiltMap C u=tilt C u :=
  tiltMap_apply_internal C u

def raw (C : Cutoff) : 𝓢(ℝ,ℂ) := 𝓕⁻ (tiltMap C)

@[expose] def φ (C : Cutoff) (ξ : ℝ) : ℂ :=
  ((scale⁻¹:ℝ):ℂ)*raw C (ξ/scale)

@[expose] def phase (ξ u : ℝ) : ℂ :=
  Complex.exp (-(ξ:ℂ)*(u:ℂ)*Complex.I)

theorem phase_norm (ξ u : ℝ) : ‖phase ξ u‖=1 := by
  simp [phase,Complex.norm_exp,Complex.mul_re,Complex.mul_im]

private theorem phase_integrable {f : ℝ→ℂ} (hf : Integrable f) (u : ℝ) :
    Integrable (fun t : ℝ => phase (scale*t) u*f t) := by
  have hp : Continuous (fun t : ℝ => phase (scale*t) u) := by
    unfold phase scale
    fun_prop
  apply hf.norm.mono' (hp.aestronglyMeasurable.mul hf.aestronglyMeasurable)
  exact Filter.Eventually.of_forall (fun t => by simp [norm_mul,phase_norm])

private theorem fourier_phase (f : ℝ→ℂ) (u : ℝ) :
    𝓕 f u = ∫ t : ℝ,phase (scale*t) u*f t := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  apply integral_congr_ae
  filter_upwards [] with t
  rw [smul_eq_mul,phase]
  congr 2
  push_cast
  unfold scale
  push_cast
  ring

/-- Exact Haar scaling from cycles to angular variables. Its leading
1/(2*pi) cancels exactly against the change of measure. -/
theorem angular_substitution (f : ℝ→ℂ) :
    (∫ ξ : ℝ,((scale⁻¹:ℝ):ℂ)*f (ξ/scale))=∫ t : ℝ,f t := by
  rw [integral_const_mul]
  have he : (fun ξ : ℝ => f (ξ/scale))=(fun ξ => f (scale⁻¹*ξ)) := by
    funext ξ
    rw [div_eq_mul_inv,mul_comm ξ]
  rw [he,Measure.integral_comp_mul_left f (scale⁻¹),inv_inv,abs_of_pos scale_pos,
    Complex.real_smul,←mul_assoc]
  have h : (scale:ℂ)≠0 := Complex.ofReal_ne_zero.mpr scale_pos.ne'
  rw [Complex.ofReal_inv,inv_mul_cancel₀ h,one_mul]

private theorem raw_inversion (C : Cutoff) :
    (𝓕 (raw C : ℝ→ℂ))=tilt C := by
  funext u
  have he : 𝓕 (raw C) = tiltMap C := by
    exact FourierTransform.fourier_fourierInv_eq (tiltMap C)
  have h := congrArg (fun f : 𝓢(ℝ,ℂ) => f u) he
  simpa only [SchwartzMap.fourier_coe,tiltMap_apply] using h

/-- Exact positive Fourier sign and the angular prefactor of the
paper transform. There is no complex conjugation. -/
theorem angular_spectrum (C : Cutoff) (ξ : ℝ) :
    φ C ξ=((scale⁻¹:ℝ):ℂ)*
      ∫ u : ℝ,Complex.exp ((ξ:ℂ)*(u:ℂ)*Complex.I)*tilt C u := by
  unfold φ raw
  rw [SchwartzMap.fourierInv_coe,Real.fourierInv_eq_fourier_neg,fourier_phase]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with u
  rw [tiltMap_apply,phase]
  congr 2
  have h : (scale:ℂ)≠0 := Complex.ofReal_ne_zero.mpr scale_pos.ne'
  push_cast
  field_simp [h] <;> ring

theorem phase_with_tilt (ξ u : ℝ) :
    Complex.exp (-mode ξ*(u:ℂ))=(Real.exp (-u):ℂ)*phase ξ u := by
  rw [Complex.ofReal_exp,phase,←Complex.exp_add]
  congr 1
  rw [mode,Complex.ofReal_neg]
  ring

private theorem raw_first (C : Cutoff) :
    Integrable (fun t : ℝ => t • raw C t) := by
  have h := (raw C).integrable_pow_mul (volume : Measure ℝ) 1
  apply h.mono' (by fun_prop)
  exact Filter.Eventually.of_forall (fun t => by simp [norm_smul])

@[expose] def rawDiff (C : Cutoff) (t : ℝ) : ℂ :=
  (-(scale:ℂ)*(t:ℂ)*Complex.I)*raw C t

private theorem rawDiff_integrable (C : Cutoff) : Integrable (rawDiff C) := by
  convert (raw_first C).const_mul (-(scale:ℂ)*Complex.I) using 1 with t
  rw [rawDiff,Complex.real_smul]
  ring

private theorem raw_derivative (C : Cutoff) (u : ℝ) :
    deriv (tilt C) u = ∫ t : ℝ,phase (scale*t) u*rawDiff C t := by
  have h := congrFun (Real.deriv_fourier (raw C).integrable (raw_first C)) u
  rw [raw_inversion C] at h
  rw [h,fourier_phase]
  apply integral_congr_ae
  filter_upwards [] with t
  rw [rawDiff,smul_eq_mul]
  unfold scale
  push_cast
  ring

private theorem tilt_derivative (C : Cutoff) (u : ℝ) :
    deriv (tilt C) u=tilt C u+(Real.exp u:ℂ)*(deriv C.χ u:ℂ) := by
  have hc := ((C.smooth.differentiable (by simp) u).hasDerivAt).ofReal_comp
  have he := (Real.hasDerivAt_exp u).ofReal_comp
  have h := (he.mul hc).deriv
  simpa [tilt,add_comm] using h

/-- Inversion of the literal chi on the real line with its moving
regulator phase. -/
theorem literal_inversion (C : Cutoff) (u : ℝ) :
    (∫ ξ : ℝ,φ C ξ*Complex.exp (-mode ξ*(u:ℂ)))=(C.χ u:ℂ) := by
  calc
    _ = (Real.exp (-u):ℂ)*
        (∫ ξ : ℝ,((scale⁻¹:ℝ):ℂ)*(phase (scale*(ξ/scale)) u*raw C (ξ/scale))) := by
      rw [←integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with ξ
      have he : scale*(ξ/scale)=ξ := by field_simp [scale_pos.ne'] <;> ring
      rw [he,φ,phase_with_tilt]
      ring
    _ = _ := by
      rw [angular_substitution,←fourier_phase,raw_inversion,tilt]
      rw [←mul_assoc,←Complex.ofReal_mul,←Real.exp_add,neg_add_cancel,Real.exp_zero]
      simp

/-- Differentiated inversion proved with the actual pinned derivative
theorem and the signed two-pi scaling. The two slots will each use
this SAME identity before squaring (not absolute-squaring a transform). -/
theorem literal_derivative (C : Cutoff) (u : ℝ) :
    (∫ ξ : ℝ,(mode ξ*φ C ξ)*Complex.exp (-mode ξ*(u:ℂ)))=
      -(deriv C.χ u:ℂ) := by
  calc
    _ = (Real.exp (-u):ℂ)*
        (∫ ξ : ℝ,((scale⁻¹:ℝ):ℂ)*
          (phase (scale*(ξ/scale)) u*(raw C (ξ/scale)-rawDiff C (ξ/scale)))) := by
      rw [←integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with ξ
      have he : scale*(ξ/scale)=ξ := by field_simp [scale_pos.ne'] <;> ring
      have hC : (scale:ℂ)≠0 := Complex.ofReal_ne_zero.mpr scale_pos.ne'
      rw [he,φ,phase_with_tilt,mode,rawDiff]
      push_cast
      field_simp [hC] <;> ring
    _ = (Real.exp (-u):ℂ)*(tilt C u-deriv (tilt C) u) := by
      rw [angular_substitution]
      have he : (fun t : ℝ => phase (scale*t) u*(raw C t-rawDiff C t)) =
          (fun t : ℝ => phase (scale*t) u*raw C t-phase (scale*t) u*rawDiff C t) := by
        funext t
        rw [mul_sub]
      rw [he,integral_sub (phase_integrable (raw C).integrable u)
        (phase_integrable (rawDiff_integrable C) u),←fourier_phase,raw_inversion,←raw_derivative]
    _ = _ := by
      rw [tilt_derivative]
      have he : tilt C u-(tilt C u+(Real.exp u:ℂ)*(deriv C.χ u:ℂ))=
          -((Real.exp u:ℂ)*(deriv C.χ u:ℂ)) := by ring
      rw [he,mul_neg,←mul_assoc,←Complex.ofReal_mul,←Real.exp_add,neg_add_cancel,Real.exp_zero]
      simp

private def scaling : ℝ ≃L[ℝ] ℝ :=
  (Units.mk0 scale⁻¹ (inv_ne_zero scale_pos.ne')) • ContinuousLinearEquiv.refl ℝ ℝ

private theorem scaling_apply (t : ℝ) : scaling t=t/scale := by
  simp only [scaling,ContinuousLinearEquiv.smul_apply,ContinuousLinearEquiv.refl_apply,
    Units.val_mk0,smul_eq_mul]
  rw [div_eq_mul_inv,mul_comm]

def angularMap (C : Cutoff) : 𝓢(ℝ,ℂ) :=
  ((scale⁻¹:ℝ):ℂ) • SchwartzMap.compCLMOfContinuousLinearEquiv ℂ scaling (raw C)

theorem angularMap_apply (C : Cutoff) (ξ : ℝ) : angularMap C ξ=φ C ξ := by
  simp only [angularMap,smul_apply,SchwartzMap.compCLMOfContinuousLinearEquiv_apply,
    Function.comp_apply,scaling_apply,smul_eq_mul,φ]

theorem angularMap_coe (C : Cutoff) : (angularMap C : ℝ→ℂ)=φ C :=
  funext (angularMap_apply C)

theorem φ_continuous (C : Cutoff) : Continuous (φ C) := by
  rw [←angularMap_coe C]
  exact (angularMap C).continuous

theorem φ_integrable (C : Cutoff) : Integrable (φ C) := by
  rw [←angularMap_coe C]
  exact (angularMap C).integrable

theorem φ_moments (C : Cutoff) (j : ℕ) :
    Integrable (fun ξ : ℝ => ‖ξ‖^j*‖φ C ξ‖) := by
  simpa only [angularMap_apply] using (angularMap C).integrable_pow_mul (volume : Measure ℝ) j

@[expose] def ψ (C : Cutoff) (ξ : ℝ) : ℂ := mode ξ*φ C ξ

theorem ψ_continuous (C : Cutoff) : Continuous (ψ C) := by
  have hm : Continuous mode := by unfold mode; fun_prop
  exact hm.mul (φ_continuous C)

theorem ψ_integrable (C : Cutoff) : Integrable (ψ C) := by
  have h₀ := (φ_integrable C).norm
  have h₁ := φ_moments C 1
  have h : Integrable (fun ξ : ℝ => (1+|ξ|)*‖φ C ξ‖) := by
    simpa only [add_mul,one_mul,pow_one,Real.norm_eq_abs] using h₀.add h₁
  apply h.mono' (ψ_continuous C).aestronglyMeasurable
  filter_upwards [] with ξ
  rw [ψ,norm_mul]
  exact mul_le_mul_of_nonneg_right (mode_norm_le ξ) (norm_nonneg _)

/-- Literal positive squarefree divisor substitution (squarefreeness
is not needed for the transform itself). No choice of branch arises
because the base of the complex power is positive real. -/
theorem divisor_inversion (C : Cutoff) (L : ℝ) (hL : 0<L) (d : ℕ) (hd : 0<d) :
    (∫ ξ : ℝ,φ C ξ*(d:ℂ)^(-(mode ξ/(L:ℂ))))=(C.χ (Real.log (d:ℝ)/L):ℂ) := by
  have hdR : (0:ℝ)<d := by exact_mod_cast hd
  have hdC : (d:ℂ)≠0 := by exact_mod_cast hd.ne'
  rw [←literal_inversion C (Real.log (d:ℝ)/L)]
  apply integral_congr_ae
  filter_upwards [] with ξ
  rw [Complex.cpow_def_of_ne_zero hdC,←Complex.ofReal_natCast,
    ←Complex.ofReal_log hdR.le,Complex.ofReal_div]
  congr 2
  have hLC : (L:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hL.ne'
  field_simp [hLC] <;> ring

/-- Uniform angular high-frequency L¹ envelope for the literal cutoff.
It follows from its actual Schwartz moment, not from a zeta bound. -/
theorem angular_tail (C : Cutoff) (j : ℕ) (H : ℝ) (hH : 0<H) :
    (∫ ξ : ℝ in {ξ : ℝ | H≤‖ξ‖},‖φ C ξ‖) ≤
      (H^j)⁻¹*(∫ ξ : ℝ,‖ξ‖^j*‖φ C ξ‖) := by
  let v : ℝ → ℝ := fun ξ => (H^j)⁻¹*(‖ξ‖^j*‖φ C ξ‖)
  have hv : Integrable v := (φ_moments C j).const_mul _
  have hs : MeasurableSet {ξ : ℝ | H≤‖ξ‖} :=
    measurableSet_le measurable_const continuous_norm.measurable
  calc
    _ ≤ ∫ ξ in {ξ : ℝ | H≤‖ξ‖},v ξ := by
      apply setIntegral_mono_on (φ_integrable C).norm.integrableOn hv.integrableOn hs
      intro ξ hξ
      have hm : H^j≤‖ξ‖^j := pow_le_pow_left₀ hH.le hξ _
      have hP : 0<H^j := pow_pos hH _
      change ‖φ C ξ‖ ≤ (H^j)⁻¹*(‖ξ‖^j*‖φ C ξ‖)
      rw [←div_eq_inv_mul]
      exact (le_div_iff₀ hP).2 (by
        rw [mul_comm]
        exact mul_le_mul_of_nonneg_right hm (norm_nonneg _))
    _ ≤ ∫ ξ : ℝ,v ξ := setIntegral_le_integral hv (Filter.Eventually.of_forall (fun _ => by
        dsimp only [v]
        positivity))
    _ = _ := by simp only [v,integral_const_mul]

end ActualTZLiteralSchwartz318
