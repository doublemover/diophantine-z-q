module
public import AnalyticFiniteRootProduct318
public import Mathlib.Tactic
public section
noncomputable section
namespace WeightedRootProductBound318
open Polynomial

/-- A weighted coefficient estimate for the literal finite root product.
The common pole weight is applied before taking a norm; no choice of a
particular coefficient or constant selected degree is required. -/
theorem coeff_bound {I : Type*} (T : Finset I) (r : I → ℂ)
    (δ B : ℝ) (hδ : 0 ≤ δ) (hB : 0 ≤ B)
    (hr : ∀ i ∈ T, δ + δ * ‖r i‖ ≤ B) (n : ℕ) :
    δ ^ T.card * ‖(∏ i ∈ T, (X - C (r i))).coeff n‖ ≤ B ^ T.card := by
  classical
  revert hr n
  induction T using Finset.induction_on with
  | empty =>
      intro hr n
      by_cases hn : n = 0
      · subst n; simp
      · simp [hn]
  | @insert i T hi ih =>
      intro hr n
      have hiB := hr i (Finset.mem_insert_self _ _)
      have htail := fun j hj => hr j (Finset.mem_insert_of_mem hj)
      have hri : 0 ≤ δ * ‖r i‖ := mul_nonneg hδ (norm_nonneg _)
      have hriB : δ * ‖r i‖ ≤ B := le_trans (le_add_of_nonneg_left hδ) hiB
      have hpow : 0 ≤ δ ^ T.card := pow_nonneg hδ _
      have hBpow : 0 ≤ B ^ T.card := pow_nonneg hB _
      rw [Finset.card_insert_of_notMem hi,Finset.prod_insert hi,pow_succ,pow_succ]
      rw [sub_mul,Polynomial.coeff_sub,Polynomial.coeff_C_mul]
      cases n with
      | zero =>
          rw [Polynomial.coeff_X_mul_zero,zero_sub,norm_neg,norm_mul]
          calc
            δ ^ T.card * δ * (‖r i‖ * ‖(∏ j ∈ T, (X - C (r j))).coeff 0‖) =
                (δ * ‖r i‖) * (δ ^ T.card * ‖(∏ j ∈ T, (X - C (r j))).coeff 0‖) := by ring
            _ ≤ B * B ^ T.card := mul_le_mul hriB (ih htail 0)
              (mul_nonneg hpow (norm_nonneg _)) hB
            _ = B ^ T.card * B := mul_comm _ _
      | succ n =>
          rw [Polynomial.coeff_X_mul]
          calc
            δ ^ T.card * δ *
                ‖(∏ j ∈ T, (X - C (r j))).coeff n -
                  r i * (∏ j ∈ T, (X - C (r j))).coeff (n+1)‖ ≤
                δ ^ T.card * δ *
                  (‖(∏ j ∈ T, (X - C (r j))).coeff n‖ +
                    ‖r i‖ * ‖(∏ j ∈ T, (X - C (r j))).coeff (n+1)‖) := by
                    apply mul_le_mul_of_nonneg_left _ (mul_nonneg hpow hδ)
                    simpa only [norm_mul] using norm_sub_le
                      ((∏ j ∈ T, (X - C (r j))).coeff n)
                      (r i * (∏ j ∈ T, (X - C (r j))).coeff (n+1))
            _ = δ * (δ ^ T.card * ‖(∏ j ∈ T, (X - C (r j))).coeff n‖) +
                (δ * ‖r i‖) * (δ ^ T.card * ‖(∏ j ∈ T, (X - C (r j))).coeff (n+1)‖) := by ring
            _ ≤ δ * B ^ T.card + (δ * ‖r i‖) * B ^ T.card :=
              add_le_add (mul_le_mul_of_nonneg_left (ih htail n) hδ)
                (mul_le_mul_of_nonneg_left (ih htail (n+1)) hri)
            _ = (δ + δ * ‖r i‖) * B ^ T.card := by ring
            _ ≤ B * B ^ T.card := mul_le_mul_of_nonneg_right hiB hBpow
            _ = B ^ T.card * B := mul_comm _ _

/-- Pad the pole weight to a fixed upper bound for the entire fiber
cardinality. This remains valid when selected degree varies or is zero. -/
theorem coeff_bound_of_card_le {I : Type*} (T : Finset I) (r : I → ℂ)
    (δ B : ℝ) (hδ : 0 ≤ δ) (hB : 0 ≤ B)
    (hr : ∀ i ∈ T, δ + δ * ‖r i‖ ≤ B) (N : ℕ) (hN : T.card ≤ N) (n : ℕ) :
    δ ^ N * ‖(∏ i ∈ T, (X - C (r i))).coeff n‖ ≤ (δ+B)^N := by
  have hk := coeff_bound T r δ B hδ hB hr n
  calc
    δ ^ N * ‖(∏ i ∈ T, (X - C (r i))).coeff n‖ =
        δ ^ (N-T.card) * (δ ^ T.card * ‖(∏ i ∈ T, (X - C (r i))).coeff n‖) := by
          rw [←mul_assoc,←pow_add,Nat.sub_add_cancel hN]
    _ ≤ δ ^ (N-T.card) * B ^ T.card :=
      mul_le_mul_of_nonneg_left hk (pow_nonneg hδ _)
    _ ≤ (δ+B) ^ (N-T.card) * (δ+B) ^ T.card :=
      mul_le_mul (pow_le_pow_left₀ hδ (le_add_of_nonneg_right hB) _)
        (pow_le_pow_left₀ hB (le_add_of_nonneg_left hδ) _)
        (pow_nonneg hB _) (pow_nonneg (add_nonneg hδ hB) _)
    _ = (δ+B)^N := by rw [←pow_add,Nat.sub_add_cancel hN]
end WeightedRootProductBound318
