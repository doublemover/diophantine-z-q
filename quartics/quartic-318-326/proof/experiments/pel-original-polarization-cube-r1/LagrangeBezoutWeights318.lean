module
public import Mathlib.LinearAlgebra.Lagrange
public import WeightedRootProductBound318
public section
noncomputable section
namespace LagrangeBezoutWeights318
open Polynomial
variable {I : Type*} [DecidableEq I]

/-- A fixed polynomial Bezout identity controls the inverse derivative
at EVERY node. This replaces individual analytic separation denominators
by evaluation of one actual coefficient polynomial. -/
theorem nodalWeight_eq (T : Finset I) (r : I → ℂ) (Q A B : Polynomial ℂ)
    (hnodal : Lagrange.nodal T r = Q) (hAB : A*Q+B*Q.derivative=1)
    (i : I) (hit : i ∈ T) : Lagrange.nodalWeight T r i = B.eval (r i) := by
  have hroot : Q.eval (r i)=0 := by
    rw [←hnodal]
    exact Lagrange.eval_nodal_at_node hit
  have h := congrArg (Polynomial.eval (r i)) hAB
  simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_one,hroot,
    mul_zero,zero_add] at h
  have hn : Q.derivative.eval (r i) ≠ 0 := right_ne_zero_of_mul_eq_one h
  rw [Lagrange.nodalWeight_eq_eval_derivative_nodal hit,hnodal]
  apply mul_right_cancel₀ hn
  rw [inv_mul_cancel₀ hn]
  exact h.symm

/-- The full interpolant is a sum of actual nodal-complement products
with weights f(r)*B(r), using the SAME Bezout polynomial for all roots. -/
theorem interpolate_eq (T : Finset I) (r a : I → ℂ) (Q A B : Polynomial ℂ)
    (hnodal : Lagrange.nodal T r = Q) (hAB : A*Q+B*Q.derivative=1) :
    Lagrange.interpolate T r a =
      ∑ i ∈ T, C (a i * B.eval (r i)) * (∏ j ∈ T.erase i, (X-C (r j))) := by
  rw [Lagrange.interpolate_eq_sum]
  apply Finset.sum_congr rfl
  intro i hit
  have hw : (∏ j ∈ T.erase i, (r i-r j))⁻¹ = B.eval (r i) := by
    calc
      _ = Lagrange.nodalWeight T r i := by
        simp only [Lagrange.nodalWeight,Finset.prod_inv_distrib]
      _ = _ := nodalWeight_eq T r Q A B hnodal hAB i hit
  rw [div_eq_mul_inv,hw]

/-- Weighted interpolation bound retaining the actual supplied values.
The fixed full fiber cardinality gives a single uniform pole exponent;
no distance-between-roots lower bound or choice of ordering is assumed. -/
theorem coefficient_bound (T : Finset I) (r a : I → ℂ) (Q A B : Polynomial ℂ)
    (hnodal : Lagrange.nodal T r = Q) (hAB : A*Q+B*Q.derivative=1)
    (δ R F G : ℝ) (hδ : 0 ≤ δ) (hR : 0 ≤ R) (hF : 0 ≤ F) (hG : 0 ≤ G)
    (hr : ∀ i ∈ T, δ + δ*‖r i‖ ≤ R)
    (ha : ∀ i ∈ T, ‖a i‖ ≤ F) (hB : ∀ i ∈ T, ‖B.eval (r i)‖ ≤ G)
    (n : ℕ) :
    δ^T.card * ‖(Lagrange.interpolate T r a).coeff n‖ ≤
      T.card * (F*G*(δ+R)^T.card) := by
  rw [interpolate_eq T r a Q A B hnodal hAB,Polynomial.finset_sum_coeff]
  calc
    δ^T.card * ‖∑ i ∈ T,
        (C (a i * B.eval (r i)) * (∏ j ∈ T.erase i, (X-C (r j)))).coeff n‖ ≤
      δ^T.card * ∑ i ∈ T,
        ‖(C (a i * B.eval (r i)) * (∏ j ∈ T.erase i, (X-C (r j)))).coeff n‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (pow_nonneg hδ _)
    _ = ∑ i ∈ T, ‖a i‖ * ‖B.eval (r i)‖ *
        (δ^T.card * ‖(∏ j ∈ T.erase i, (X-C (r j))).coeff n‖) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Polynomial.coeff_C_mul,norm_mul,norm_mul]
      ring
    _ ≤ ∑ i ∈ T, F*G*(δ+R)^T.card := by
      apply Finset.sum_le_sum
      intro i hit
      have hp := WeightedRootProductBound318.coeff_bound_of_card_le (T.erase i) r δ R hδ hR
        (fun j hj => hr j (Finset.mem_erase.mp hj).2) T.card (Finset.card_le_card (Finset.erase_subset _ _)) n
      exact mul_le_mul
        (mul_le_mul (ha i hit) (hB i hit) (norm_nonneg _) hF) hp
        (mul_nonneg (pow_nonneg hδ _) (norm_nonneg _)) (mul_nonneg hF hG)
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]
end LagrangeBezoutWeights318
