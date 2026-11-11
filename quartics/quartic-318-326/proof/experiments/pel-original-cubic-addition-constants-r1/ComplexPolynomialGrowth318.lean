module
public import Mathlib.Analysis.Complex.Liouville
public import Mathlib.Analysis.Complex.TaylorSeries
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Algebra.Polynomial.BigOperators
public section
noncomputable section
namespace ComplexPolynomialGrowth318
open Set Filter Polynomial
open scoped Topology BigOperators

/-- Cauchy estimates force every derivative above a genuine uniform
polynomial growth degree to vanish. No polynomiality premise is used. -/
theorem high_derivative_zero (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (N : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ R : ℝ, 1 ≤ R → ∀ z : ℂ, ‖z‖ = R → ‖f z‖ ≤ C * R ^ N)
    (n : ℕ) (hn : N < n) : iteratedDeriv n f 0 = 0 := by
  apply norm_le_zero_iff.mp
  apply le_of_forall_gt_imp_ge_of_dense
  intro ε hε
  let K : ℝ := (n.factorial : ℝ) * C
  let R : ℝ := max 1 (K / ε) + 1
  have hR1 : 1 < R := by dsimp [R]; linarith [le_max_left (1 : ℝ) (K/ε)]
  have hR : 0 < R := lt_trans zero_lt_one hR1
  have hKe : K / ε < R := by dsimp [R]; linarith [le_max_right (1 : ℝ) (K/ε)]
  have hp : R ^ (N+1) ≤ R ^ n := pow_le_pow_right₀ hR1.le (by omega)
  have hbound : ‖iteratedDeriv n f 0‖ ≤ (n.factorial : ℝ) * (C * R ^ N) / R ^ n := by
    apply Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n hR hf.diffContOnCl
    intro z hz
    apply hb R hR1.le z
    simpa only [Metric.mem_sphere,dist_zero_right] using hz
  have hquot : (n.factorial : ℝ) * (C * R ^ N) / R ^ n ≤ K / R := by
    apply (div_le_div_iff₀ (pow_pos hR n) hR).mpr
    have hm := mul_le_mul_of_nonneg_left hp (show 0 ≤ K by dsimp [K]; positivity)
    rw [pow_succ] at hm
    dsimp [K] at ⊢ hm
    nlinarith
  exact hbound.trans (hquot.trans ((div_le_iff₀ hR).mpr
    (le_of_lt (by nlinarith [(div_lt_iff₀ hε).mp hKe]))))

/-- The Taylor polynomial is an actual polynomial representing an entire
function with uniform degree-N growth. The degree bound is retained for
later finite interpolation, not merely existence of some polynomial. -/
theorem exists_polynomial (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (N : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ R : ℝ, 1 ≤ R → ∀ z : ℂ, ‖z‖ = R → ‖f z‖ ≤ C * R ^ N) :
    ∃ p : ℂ[X], p.natDegree ≤ N ∧ ∀ z : ℂ, p.eval z = f z := by
  classical
  let p : ℂ[X] := ∑ n ∈ Finset.range (N+1),
    Polynomial.monomial n ((n.factorial : ℂ)⁻¹ * iteratedDeriv n f 0)
  have hd : p.natDegree ≤ N := by
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro k hk
    exact (Polynomial.natDegree_monomial_le _).trans (by
      have := Finset.mem_range.mp hk
      omega)
  refine ⟨p,hd,?_⟩
  intro z
  have ht := Complex.taylorSeries_eq_of_entire' hf (c := 0) (z := z)
  rw [tsum_eq_sum (s := Finset.range (N+1))] at ht
  · simpa only [p,Polynomial.eval_finsetSum,Polynomial.eval_monomial,sub_zero] using ht
  · intro n hn
    have hN : N < n := by
      have := Finset.notMem_range.mp hn
      omega
    rw [high_derivative_zero f hf N C hC hb n hN,mul_zero,zero_mul]
end ComplexPolynomialGrowth318
