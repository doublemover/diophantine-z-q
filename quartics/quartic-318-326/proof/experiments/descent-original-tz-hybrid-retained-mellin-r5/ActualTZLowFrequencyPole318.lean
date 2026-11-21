module
public import ActualTZMellinKernel318
public import ActualTZZetaPoleRatio318
public section
noncomputable section
namespace ActualTZLowFrequencyPole318
open ActualTZMellinKernel318 ActualTZZetaPoleRatio318

@[expose] def band (L : ℝ) : ℝ := L^((1:ℝ)/4)
@[expose] def shift (L ξ : ℝ) : ℂ := mode ξ/(L:ℂ)

theorem shift_re (L ξ : ℝ) : (shift L ξ).re=1/L := by
  rw [shift,Complex.div_ofReal_re,mode_re]

private theorem shift_ne_zero (L ξ : ℝ) (hL : 0<L) : shift L ξ≠0 := by
  intro h
  have he := shift_re L ξ
  rw [h,Complex.zero_re] at he
  exact (ne_of_gt (one_div_pos.mpr hL)) he.symm

private theorem sum_ne_zero (L ξ η : ℝ) (hL : 0<L) : shift L ξ+shift L η≠0 := by
  intro h
  have he : (shift L ξ+shift L η).re=1/L+1/L := by
    rw [Complex.add_re,shift_re,shift_re]
  rw [h,Complex.zero_re] at he
  exact (ne_of_gt (by positivity : 0<1/L+1/L)) he.symm

private theorem residue_ne (L ξ : ℝ) (hL : 0<L) : residueFactor (shift L ξ)≠0 := by
  apply mul_ne_zero (shift_ne_zero L ξ hL)
  apply riemannZeta_ne_zero_of_one_le_re
  rw [Complex.add_re,Complex.one_re,shift_re]
  linarith [one_div_pos.mpr hL]

private theorem norm_bound (L ξ : ℝ) (hL : 1≤L) (hξ : |ξ|≤band L) :
    ‖shift L ξ‖≤2/Real.sqrt L := by
  have hp : 0<L := zero_lt_one.trans_le hL
  have hroot : 0<Real.sqrt L := Real.sqrt_pos.mpr hp
  have h₁ : (1:ℝ)≤Real.sqrt L := (Real.le_sqrt zero_le_one hp.le).2 (by simpa using hL)
  have hξ' : |ξ|≤Real.sqrt L := hξ.trans (by
    rw [band,Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hL (by norm_num))
  rw [shift,norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hp]
  apply (div_le_div_iff₀ hp hroot).2
  have H : ‖mode ξ‖≤2*Real.sqrt L := by linarith [mode_norm_le ξ]
  calc
    _ ≤ (2*Real.sqrt L)*Real.sqrt L := mul_le_mul_of_nonneg_right H hroot.le
    _ = _ := by rw [mul_assoc,←pow_two,Real.sq_sqrt hp.le]

/-- One absolute disk works simultaneously for both literal
frequencies and their sum on the moving band |ξ|,|η|≤L^(1/4).
The explicit threshold uses a deliberately weaker sqrt estimate,
not a change to the true Fourier truncation. -/
theorem disk_on_band (r : ℝ) (hr : 0<r) :
    ∃ L₀≥(1:ℝ),∀ L≥L₀,∀ ξ η : ℝ, |ξ|≤band L → |η|≤band L →
      ‖shift L ξ‖<r ∧ ‖shift L η‖<r ∧ ‖shift L ξ+shift L η‖<r := by
  let A := 1+4/r
  have hA : 0<A := by dsimp only [A]; positivity
  refine ⟨max 1 (A^2),le_max_left _ _,?_⟩
  intro L hL ξ η hξ hη
  have h₁ : 1≤L := (le_max_left _ _).trans hL
  have hA' : A≤Real.sqrt L := (Real.le_sqrt hA.le ((zero_le_one : (0:ℝ)≤1).trans h₁)).2
    ((le_max_right _ _).trans hL)
  have hR : 4/r<Real.sqrt L := by dsimp only [A] at hA'; linarith
  have h4 : 4<Real.sqrt L*r := (div_lt_iff₀ hr).1 hR
  have he : 2/Real.sqrt L<r/2 := by
    have hp := Real.sqrt_pos.mpr (zero_lt_one.trans_le h₁)
    apply (div_lt_div_iff₀ hp (by norm_num : (0:ℝ)<2)).2
    linarith only [h4]
  have Hξ := (norm_bound L ξ h₁ hξ).trans_lt he
  have Hη := (norm_bound L η h₁ hη).trans_lt he
  exact ⟨Hξ.trans (by linarith),Hη.trans (by linarith),
    (norm_add_le _ _).trans_lt (by linarith only [Hξ,Hη])⟩

@[expose] def correction (L ξ η : ℝ) : ℂ :=
  residueFactor (shift L ξ+shift L η)/
    (residueFactor (shift L ξ)*residueFactor (shift L η))

theorem scaled_zeta_identity (L ξ η : ℝ) (hL : 0<L) :
    (L:ℂ)*ratio (shift L ξ) (shift L η)=kernel ξ η*correction L ξ η := by
  have hscale : (L:ℂ)*(shift L ξ*shift L η/(shift L ξ+shift L η))=kernel ξ η :=
    kernel_scale L ξ η hL.ne'
  rw [ratio_factor _ _ (shift_ne_zero L ξ hL) (shift_ne_zero L η hL)
    (sum_ne_zero L ξ η hL) (residue_ne L ξ hL) (residue_ne L η hL),correction,←mul_assoc,hscale]

/-- The literal normalized low-band ζ ratio has one same relative
bound at all admissible frequencies, for arbitrary ε before L is
selected. This is enough for the later integrated main comparison. -/
theorem correction_uniform (ε : ℝ) (hε : 0<ε) (hε' : ε≤1/2) :
    ∃ L₀≥(1:ℝ),∀ L≥L₀,∀ ξ η : ℝ, |ξ|≤band L → |η|≤band L →
        ‖correction L ξ η-1‖≤14*ε := by
  obtain ⟨r,hr,H⟩ := residue_uniform ε hε
  obtain ⟨L₀,h₀,hD⟩ := disk_on_band r hr
  refine ⟨L₀,h₀,?_⟩
  intro L hL ξ η hξ hη
  have hp := zero_lt_one.trans_le (h₀.trans hL)
  obtain ⟨Hξ,Hη,Hs⟩ := hD L hL ξ η hξ hη
  exact correction_bound _ _ _ ε hε'
    (H _ (sum_ne_zero L ξ η hp) Hs).le
    (H _ (shift_ne_zero L ξ hp) Hξ).le
    (H _ (shift_ne_zero L η hp) Hη).le

end ActualTZLowFrequencyPole318
