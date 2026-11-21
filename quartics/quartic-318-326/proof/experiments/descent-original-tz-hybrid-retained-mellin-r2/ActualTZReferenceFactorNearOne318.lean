module
public import ActualTZRegulatedZetaAlgebra318
public import ActualTZMovingReferenceTail318
public section
noncomputable section
namespace ActualTZReferenceFactorNearOne318
open ActualTZRegulatedZetaAlgebra318 ActualTZPositiveEulerMajorant318

/-- Keep exact overlap phase and gain an extra full p^(-σ) on the
all-frequency first-order reference factor. -/
theorem local_distance (x z w : ℂ) (θ : ℝ)
    (hx : ‖x‖≤1/2) (hθ : θ≤1) (hz : ‖z‖≤θ) (hw : ‖w‖≤θ) :
    ‖oneSite x z w-1‖≤7*‖x‖*θ := by
  have hθ0 := (norm_nonneg z).trans hz
  have hl := denominator_lower x z w hx (hz.trans hθ) (hw.trans hθ)
  have hden : 1-x*z*w≠0 := by
    intro h
    rw [h,norm_zero] at hl
    norm_num at hl
  have hn : oneSite x z w-1 =
      (-(x*z)-x*w+x*z*w+x*x*z*w)/(1-x*z*w) := by
    unfold oneSite
    field_simp [hden] <;> ring
  have h₁ : ‖x*z‖≤‖x‖*θ := by
    rw [norm_mul]; exact mul_le_mul_of_nonneg_left hz (norm_nonneg x)
  have h₂ : ‖x*w‖≤‖x‖*θ := by
    rw [norm_mul]; exact mul_le_mul_of_nonneg_left hw (norm_nonneg x)
  have h₃ : ‖x*z*w‖≤‖x‖*θ := by
    rw [norm_mul]
    calc
      _ ≤ (‖x‖*θ)*1 := mul_le_mul h₁ (hw.trans hθ) (norm_nonneg _) zero_le_one
      _ = _ := mul_one _
  have h₄ : ‖x*x*z*w‖≤((1:ℝ)/2)*(‖x‖*θ) := by
    have h : x*x*z*w=x*(x*z*w) := by ring
    rw [h,norm_mul]
    exact mul_le_mul hx h₃ (norm_nonneg _) (by norm_num)
  rw [hn,norm_div]
  apply (div_le_iff₀ (show 0<‖1-x*z*w‖ by linarith)).2
  have B : ‖-(x*z)-x*w+x*z*w+x*x*z*w‖≤
      ‖x*z‖+‖x*w‖+‖x*z*w‖+‖x*x*z*w‖ := by
    calc
      _ ≤ ‖-(x*z)-x*w+x*z*w‖+‖x*x*z*w‖ := norm_add_le _ _
      _ ≤ (‖-(x*z)-x*w‖+‖x*z*w‖)+‖x*x*z*w‖ := by
        gcongr
        exact norm_add_le _ _
      _ ≤ _ := by
        gcongr
        simpa only [norm_neg] using norm_sub_le (-(x*z)) (x*w)
  have H := mul_le_mul_of_nonneg_left hl (by positivity : 0≤7*‖x‖*θ)
  linarith

@[expose] def B (p : ℕ) (s t : ℂ) : ℂ :=
  oneSite (1/(p:ℂ)) ((p:ℂ)^(-s)) ((p:ℂ)^(-t))

/-- This is the precise moving-regulator p^-1-σ envelope, valid at
unbounded imaginary frequencies. -/
theorem at_regulator (σ : ℝ) (hσ : 0<σ) (p : ℕ) (hp : p.Prime)
    (s t : ℂ) (hs : σ≤s.re) (ht : σ≤t.re) :
    ‖B p s t-1‖≤7*q σ p := by
  let θ := (p:ℝ)^(-σ)
  have hpR : 0<(p:ℝ) := by exact_mod_cast hp.pos
  have hp1 : (1:ℝ)≤p := by exact_mod_cast hp.one_lt.le
  have hx : ‖(1:ℂ)/(p:ℂ)‖≤(1:ℝ)/2 := by
    rw [norm_div,norm_one,Complex.norm_natCast]
    exact div_le_div_of_nonneg_left zero_le_one (by norm_num) (by exact_mod_cast hp.two_le)
  have hθ : θ≤1 := Real.rpow_le_one_of_one_le_of_nonpos hp1 (neg_nonpos.mpr hσ.le)
  have hz : ‖(p:ℂ)^(-s)‖≤θ := by
    rw [Complex.norm_natCast_cpow_of_pos hp.pos,Complex.neg_re]
    exact Real.rpow_le_rpow_of_exponent_le hp1 (neg_le_neg hs)
  have hw : ‖(p:ℂ)^(-t)‖≤θ := by
    rw [Complex.norm_natCast_cpow_of_pos hp.pos,Complex.neg_re]
    exact Real.rpow_le_rpow_of_exponent_le hp1 (neg_le_neg ht)
  apply (local_distance _ _ _ θ hx hθ hz hw).trans_eq
  rw [norm_div,norm_one,Complex.norm_natCast,q,
    show -1-σ=(-σ)-(1:ℝ) by ring,Real.rpow_sub hpR,Real.rpow_one]
  dsimp only [θ]
  ring

end ActualTZReferenceFactorNearOne318
