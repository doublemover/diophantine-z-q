module
public import ActualFiniteEulerExclusions318
public section
noncomputable section
namespace ActualSelectedEulerLower318
open scoped BigOperators
open ActualOrdinaryEulerHarmonic318 ActualFiniteEulerExclusions318 ActualOriginalEulerComparison318
open ActualCharacterFiniteLogControl318 ActualModFourSieveCharacter318 ActualGlobalCharacterLower318
set_option maxHeartbeats 18000000
variable {J : Type*} [Fintype J] [DecidableEq J]

/-- Ordinary logarithmic growth survives deletion of precisely the
original finite exceptional and small-prime set. -/
theorem actual_selected_ordinary_lower (κ : ℤ) (γ : J → ℤ) :
    ∃ U : ℝ,0<U ∧ ∀ N,1≤N → Real.log (N:ℝ)/U≤ordinaryEuler κ γ N := by
  have hf (p : ℕ) (hp : p.Prime) : 0<(1-1/(p:ℝ))⁻¹ := by
    have hh := ActualCharacterPowerShift318.prime_inverse_half p hp
    apply inv_pos.mpr
    linarith
  obtain ⟨U,hU,hbound⟩ := actual_selected_product_comparison κ γ
    (fun p => (1-1/(p:ℝ))⁻¹) hf
  refine ⟨U,hU,?_⟩
  intro N hN
  have hh := (actual_ordinary_log_lower N hN).trans (hbound N)
  apply (div_le_iff₀ hU).mpr
  simpa only [ordinaryEuler,mul_comm] using hh

/-- The genuine global mod-four character lower bound survives the
SAME original prime exclusions. The finite removed factors are bounded
as actual positive subproducts, even when some are less than1. -/
theorem actual_selected_character_lower (κ : ℤ) (γ : J → ℤ) :
    ∃ c : ℝ,0<c ∧ ∀ N,c≤characterEuler κ γ N := by
  obtain ⟨c,hc,hclower⟩ := actual_global_character_lower
  have hf (p : ℕ) (hp : p.Prime) : 0<(1-realCharacter p/(p:ℝ))⁻¹ := by
    have hh := ActualCharacterLogFactor318.actual_factor_positive 1 le_rfl p hp
    apply inv_pos.mpr
    simpa only [Real.rpow_neg_one,div_eq_mul_inv] using hh
  obtain ⟨U,hU,hbound⟩ := actual_selected_product_comparison κ γ
    (fun p => (1-realCharacter p/(p:ℝ))⁻¹) hf
  refine ⟨c/U,div_pos hc hU,?_⟩
  intro N
  have hfull : c≤∏p∈Nat.primesBelow N,(1-realCharacter p/(p:ℝ))⁻¹ := by
    simpa only [finiteEuler,Real.rpow_neg_one,div_eq_mul_inv] using hclower N
  have hh := hfull.trans (hbound N)
  apply (div_le_iff₀ hU).mpr
  simpa only [characterEuler,mul_comm] using hh

end ActualSelectedEulerLower318
