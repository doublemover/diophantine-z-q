module
public import GlobalSaturationHeight318
public section
namespace DuplicationHeightArch318
open ConcreteG8Domain
set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-- Explicit archimedean duplication bounds, with the same constant 676
as the saturation argument and no implicit norm-equivalence constant. -/
theorem real_duplication_bounds (a b d:ℝ) (hd:1≤d) (hD:d≤25) :
    (max |a| |b|)^4≤max |(a^2+d*b^2)^2| |4*a*b*(a^2-d*b^2)| ∧
    max |(a^2+d*b^2)^2| |4*a*b*(a^2-d*b^2)|≤676*(max |a| |b|)^4 := by
  let M := max |a| |b|
  have hM : 0≤M := (abs_nonneg a).trans (le_max_left _ _)
  have ha : |a|≤M := le_max_left _ _
  have hb : |b|≤M := le_max_right _ _
  have ha2 : a^2≤M^2 := by simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg a) hM).mpr ha
  have hb2 : b^2≤M^2 := by simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg b) hM).mpr hb
  have hd0 : 0≤d := by linarith
  have hS0 : 0≤a^2+d*b^2 := add_nonneg (sq_nonneg _) (mul_nonneg hd0 (sq_nonneg _))
  have hS : a^2+d*b^2≤26*M^2 := by
    have h1 := mul_le_mul_of_nonneg_left hb2 hd0
    have h2 := mul_le_mul_of_nonneg_right hD (sq_nonneg M)
    nlinarith
  have hF : |(a^2+d*b^2)^2|≤676*M^4 := by
    rw [abs_of_nonneg (sq_nonneg (a^2+d*b^2))]
    nlinarith [mul_nonneg (sub_nonneg.mpr hS) (add_nonneg (by positivity : 0≤26*M^2) hS0)]
  have hp : |a| *|b|≤M^2 := by
    calc
      _ ≤ M*M := mul_le_mul ha hb (abs_nonneg _) hM
      _ = _ := by ring
  have hdiff : |a^2-d*b^2|≤a^2+d*b^2 := by
    calc
      _ ≤ |a^2|+|d*b^2| := by simpa only [sub_zero,zero_sub,abs_neg] using (abs_sub_le (a^2) 0 (d*b^2))
      _ = _ := by rw [abs_of_nonneg (sq_nonneg _),abs_of_nonneg (mul_nonneg hd0 (sq_nonneg _))]
  have hG : |4*a*b*(a^2-d*b^2)|≤104*M^4 := by
    calc
      _ = 4*(|a| *|b|)*|a^2-d*b^2| := by rw [abs_mul,abs_mul,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<4)]; ring
      _ ≤ (4*M^2)*(a^2+d*b^2) := mul_le_mul
        (by nlinarith : 4*(|a| *|b|)≤4*M^2) hdiff (abs_nonneg _) (by positivity)
      _ ≤ (4*M^2)*(26*M^2) := mul_le_mul_of_nonneg_left hS (by positivity)
      _ = 104*M^4 := by ring
  constructor
  · apply le_trans (b:=|(a^2+d*b^2)^2|) _ (le_max_left _ _)
    rw [abs_of_nonneg (sq_nonneg (a^2+d*b^2))]
    rcases le_total |a| |b| with hab|hba
    · have hh : b^2≤a^2+d*b^2 := by nlinarith [sq_nonneg a,sq_nonneg b]
      rw [max_eq_right hab]
      nlinarith [sq_abs b,mul_nonneg (sub_nonneg.mpr hh) (add_nonneg hS0 (sq_nonneg b))]
    · have hh : a^2≤a^2+d*b^2 := by nlinarith [sq_nonneg b]
      rw [max_eq_left hba]
      nlinarith [sq_abs a,mul_nonneg (sub_nonneg.mpr hh) (add_nonneg hS0 (sq_nonneg a))]
  · apply max_le hF
    exact hG.trans (by nlinarith [pow_nonneg hM 4])

theorem conjugate_D_bounds (s:ℝ) (hs:s^2=2) : 1≤(3-s)^2 ∧ (3-s)^2≤25 := by
  have hlo : -2<s := by nlinarith
  have hhi : s<2 := by nlinarith
  constructor <;> nlinarith

/-- The same constants hold at every actual real embedding of Q(sqrt2). -/
theorem embedding_duplication_bounds (σ:K→+*ℝ) (a b:K) :
    (max |σ a| |σ b|)^4≤max |σ ((a^2+D*b^2)^2)| |σ (4*a*b*(a^2-D*b^2))| ∧
    max |σ ((a^2+D*b^2)^2)| |σ (4*a*b*(a^2-D*b^2))|≤676*(max |σ a| |σ b|)^4 := by
  have hi : i^2=(2:K) := by ext <;> norm_num [i,pair,pow_succ]
  have hs : (σ i)^2=(2:ℝ) := by simpa only [map_pow,map_ofNat] using congrArg σ hi
  have hd : σ D=(3-σ i)^2 := by rw [D,map_pow,map_sub,map_ofNat]
  obtain ⟨hl,hu⟩ := conjugate_D_bounds (σ i) hs
  have hh := real_duplication_bounds (σ a) (σ b) ((3-σ i)^2) hl hu
  simpa only [map_pow,map_add,map_mul,map_sub,map_ofNat,hd] using hh

end DuplicationHeightArch318
