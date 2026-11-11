module
public import RealEulerLogLipschitz318
public section
noncomputable section
namespace ActualCharacterPowerShift318
open ZMod ActualModFourSieveCharacter318
set_option maxHeartbeats 18000000

lemma character_abs_le_one (p : ℕ) : |realCharacter p|≤1 := by
  have hh := isQuadratic_χ₄ (p:ZMod 4)
  rcases hh with h|h|h <;> simp only [realCharacter,h] <;> norm_num
lemma prime_inverse_half (p : ℕ) (hp : p.Prime) : 1/(p:ℝ)≤1/2 :=
  one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast hp.two_le)

lemma prime_power_small (p : ℕ) (hp : p.Prime) (σ : ℝ) (hσ : 1≤σ) :
    0≤(p:ℝ)^(-σ) ∧ (p:ℝ)^(-σ)≤1/2 := by
  have hp1 : (1:ℝ)≤p := by exact_mod_cast hp.one_le
  have hh := Real.rpow_le_rpow_of_exponent_le hp1 (show -σ≤ -1 by linarith)
  rw [Real.rpow_neg_one] at hh
  exact ⟨Real.rpow_nonneg (Nat.cast_nonneg _) _,
    hh.trans (by simpa only [one_div] using prime_inverse_half p hp)⟩

/-- Exact shift in the original reciprocal-prime argument when the
real exponent moves from1 to1+delta. It is bounded before summing. -/
lemma actual_power_difference (p : ℕ) (hp : p.Prime) (δ : ℝ) (hδ : 0≤δ) :
    0≤1/(p:ℝ)-(p:ℝ)^(-(1+δ)) ∧
      1/(p:ℝ)-(p:ℝ)^(-(1+δ))≤δ*Real.log (p:ℝ)/(p:ℝ) := by
  have hp0 : (0:ℝ)<p := by exact_mod_cast hp.pos
  have hl : 0≤Real.log (p:ℝ) := Real.log_natCast_nonneg _
  let x := δ*Real.log (p:ℝ)
  have hx : 0≤x := mul_nonneg hδ hl
  have he : (p:ℝ)^(-(1+δ))=(1/(p:ℝ))*Real.exp (-x) := by
    have hexp : -(1+δ)=(-1:ℝ)+(-δ) := by ring
    rw [hexp,Real.rpow_add hp0,Real.rpow_neg_one,Real.rpow_def_of_pos hp0]
    congr 1
    · exact (one_div _).symm
    · congr 1
      dsimp [x]
      ring
  have he1 : Real.exp (-x)≤1 := Real.exp_le_one_iff.mpr (by linarith)
  have he2 : 1-Real.exp (-x)≤x := by
    have hh := Real.add_one_le_exp (-x)
    linarith
  have hpos : 0≤1/(p:ℝ) := (div_pos (by norm_num) hp0).le
  have hlow := mul_nonneg hpos (show 0≤1-Real.exp (-x) by linarith)
  have hu := mul_le_mul_of_nonneg_left he2 hpos
  rw [he]
  constructor
  · nlinarith only [hlow]
  · dsimp [x] at hu
    convert hu using 1 <;> ring

lemma actual_character_argument_shift (p : ℕ) (hp : p.Prime) (δ : ℝ) (hδ : 0≤δ) :
    |realCharacter p/(p:ℝ)-realCharacter p*(p:ℝ)^(-(1+δ))|≤
      δ*Real.log (p:ℝ)/(p:ℝ) := by
  obtain ⟨h0,h1⟩ := actual_power_difference p hp δ hδ
  have he : realCharacter p/(p:ℝ)-realCharacter p*(p:ℝ)^(-(1+δ))=
      realCharacter p*(1/(p:ℝ)-(p:ℝ)^(-(1+δ))) := by ring
  rw [he,abs_mul,abs_of_nonneg h0]
  exact (mul_le_mul_of_nonneg_right (character_abs_le_one p) h0).trans
    (by simpa only [one_mul] using h1)

lemma argument_small (p : ℕ) (hp : p.Prime) (σ : ℝ) (hσ : 1≤σ) :
    |realCharacter p*(p:ℝ)^(-σ)|≤1/2 := by
  obtain ⟨h0,h1⟩ := prime_power_small p hp σ hσ
  rw [abs_mul,abs_of_nonneg h0]
  exact (mul_le_mul_of_nonneg_right (character_abs_le_one p) h0).trans
    (by simpa only [one_mul] using h1)

end ActualCharacterPowerShift318
