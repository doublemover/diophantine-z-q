module
public import EulerBinomialError318
public section
noncomputable section
namespace SieveEulerCorrection318
open EulerBinomialError318
set_option maxHeartbeats 1000000

@[expose] def errorConstant (k : ℕ) : ℝ := 8*(4*(k:ℝ)^2+7*(k:ℝ)+5)
@[expose] def correction (k : ℕ) (x e g : ℝ) : ℝ := (1-g)/model k x e

/-- Actual local first-order errors become absolutely summable quadratic
errors after removing BOTH ordinary and quadratic-character Euler factors. -/
theorem correction_error (k : ℕ) (x e g : ℝ) (hx : 0≤x) (hxhalf : x≤1/2)
    (hkx : (k:ℝ)*x≤1/2) (he : e=1 ∨ e= -1)
    (hg : |g-((k:ℝ)+2*e)*x|≤4*((k:ℝ)+1)*x^2) :
    |correction k x e g-1|≤errorConstant k*x^2 := by
  have hM := model_lower k x e hx hxhalf hkx he
  have hMp : 0<model k x e := by linarith
  have hmerr := model_error k x e hx (by linarith) he
  have hn : |(1-g)-model k x e|≤(4*(k:ℝ)^2+7*(k:ℝ)+5)*x^2 := by
    obtain ⟨hg0,hg1⟩ := abs_le.mp hg
    obtain ⟨hm0,hm1⟩ := abs_le.mp hmerr
    rw [abs_le]
    constructor <;> nlinarith
  have hid : correction k x e g-1=((1-g)-model k x e)/model k x e := by
    dsimp [correction]
    field_simp [ne_of_gt hMp]
    <;> ring
  rw [hid,abs_div,abs_of_pos hMp]
  apply (div_le_iff₀ hMp).mpr
  have hc : 0≤errorConstant k*x^2 := by dsimp [errorConstant]; positivity
  have hh := mul_le_mul_of_nonneg_left hM hc
  dsimp [errorConstant] at hh ⊢
  nlinarith

/-- The large-prime correction is genuinely positive, not only nonzero. -/
theorem correction_positive (k : ℕ) (x e g : ℝ) (hx : 0≤x)
    (hsmall : ((k:ℝ)+2)*x≤1/16) (he : e=1 ∨ e= -1)
    (hg : |g-((k:ℝ)+2*e)*x|≤4*((k:ℝ)+1)*x^2) :
    0<correction k x e g := by
  have hk0 : (0:ℝ)≤k := Nat.cast_nonneg k
  have hkx0 : 0≤(k:ℝ)*x := mul_nonneg hk0 hx
  have hx16 : x≤1/16 := by nlinarith
  have hkx16 : ((k:ℝ)+1)*x≤1/16 := by nlinarith
  have hsq : ((k:ℝ)+1)*x^2≤1/256 := by
    have hh := mul_le_mul hkx16 hx16 hx (by norm_num : (0:ℝ)≤1/16)
    nlinarith
  have hlinear : ((k:ℝ)+2*e)*x≤1/16 := by
    rcases he with rfl|rfl <;> nlinarith
  have hgn : g<1 := by have hh := (abs_le.mp hg).2; nlinarith
  apply div_pos (by linarith) (lt_of_lt_of_le (by norm_num : (0:ℝ)<1/8) _)
  exact model_lower k x e hx (by linarith) (by nlinarith) he

end SieveEulerCorrection318
