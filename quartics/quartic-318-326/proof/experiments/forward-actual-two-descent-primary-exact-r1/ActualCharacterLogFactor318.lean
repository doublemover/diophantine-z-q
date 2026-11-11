module
public import ActualCharacterPowerShift318
public section
noncomputable section
namespace ActualCharacterLogFactor318
open ActualModFourSieveCharacter318 ActualCharacterPowerShift318 RealEulerLogLipschitz318
set_option maxHeartbeats 16000000

@[expose] def logFactor (σ : ℝ) (p : ℕ) : ℝ :=
  -Real.log (1-realCharacter p*(p:ℝ)^(-σ))

lemma actual_factor_positive (σ : ℝ) (hσ : 1≤σ) (p : ℕ) (hp : p.Prime) :
    0<1-realCharacter p*(p:ℝ)^(-σ) := by
  have hh := (abs_le.mp (argument_small p hp σ hσ)).2
  linarith

/-- Original real-character Euler logarithm is bounded uniformly by
twice the ACTUAL shifted prime power. -/
lemma actual_log_factor_bound (σ : ℝ) (hσ : 1≤σ) (p : ℕ) (hp : p.Prime) :
    |logFactor σ p|≤2*(p:ℝ)^(-σ) := by
  have hh := one_sub_log_bound (realCharacter p*(p:ℝ)^(-σ)) (argument_small p hp σ hσ)
  have hp0 := (prime_power_small p hp σ hσ).1
  have ha : |realCharacter p*(p:ℝ)^(-σ)|≤(p:ℝ)^(-σ) := by
    rw [abs_mul,abs_of_nonneg hp0]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right (character_abs_le_one p) hp0
  unfold logFactor
  rw [abs_neg]
  exact hh.trans (mul_le_mul_of_nonneg_left ha (by norm_num))

/-- Exact original Euler logarithm shift from exponent1 to1+delta.
No derivative convention or unproved uniform little-o term is used. -/
lemma actual_log_factor_shift (p : ℕ) (hp : p.Prime) (δ : ℝ) (hδ : 0≤δ) :
    |logFactor 1 p-logFactor (1+δ) p|≤2*δ*Real.log (p:ℝ)/(p:ℝ) := by
  have h1 := argument_small p hp 1 le_rfl
  have h2 := argument_small p hp (1+δ) (by linarith)
  have hl := one_sub_log_lipschitz
    (realCharacter p*(p:ℝ)^(-(1:ℝ)))
    (realCharacter p*(p:ℝ)^(-(1+δ))) h1 h2
  have ha : |realCharacter p*(p:ℝ)^(-(1:ℝ))-realCharacter p*(p:ℝ)^(-(1+δ))|≤
      δ*Real.log (p:ℝ)/(p:ℝ) := by
    simpa only [Real.rpow_neg_one,div_eq_mul_inv] using actual_character_argument_shift p hp δ hδ
  have hu := mul_le_mul_of_nonneg_left ha (by norm_num : (0:ℝ)≤2)
  unfold logFactor
  rw [neg_sub_neg,abs_sub_comm]
  exact hl.trans (by convert hu using 1 <;> ring)

end ActualCharacterLogFactor318
