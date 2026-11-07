module
public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.QExpansion
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Tactic
public section
noncomputable section
open Set Metric UpperHalfPlane ModularFormClass
open scoped ArithmeticFunction.sigma
namespace E4Producer318
set_option maxHeartbeats 0

/-- The actual normalized weight-four Eisenstein series in the cusp coordinate. -/
@[expose] def E4 : ℂ → ℂ := cuspFunction 1 (ModularForm.E (k := 4) (by norm_num))

theorem E4_holomorphic : DifferentiableOn ℂ E4 (ball 0 1) := by
  intro q hq
  exact (ModularFormClass.differentiableAt_cuspFunction
    (ModularForm.E (k := 4) (by norm_num)) (by norm_num)
    one_mem_strictPeriods_SL (by simpa using hq)).differentiableWithinAt

theorem E4_qParam (z : UpperHalfPlane) :
    E4 (Function.Periodic.qParam 1 z) = ModularForm.E (k := 4) (by norm_num) z :=
  SlashInvariantFormClass.eq_cuspFunction _ z one_mem_strictPeriods_SL (by norm_num)

theorem E4_coeff (n : ℕ) :
    (qExpansion 1 (ModularForm.E (k := 4) (by norm_num))).coeff n =
      if n = 0 then 1 else (240 : ℂ) * (ArithmeticFunction.sigma 3 n : ℂ) := by
  have h := EisensteinSeries.E_qExpansion_coeff (k := 4) (by norm_num) (by norm_num) n
  norm_num [bernoulli_eq_bernoulli'_of_ne_one (by norm_num : 4 ≠ 1)] at h ⊢
  exact h

theorem E4_zero : E4 0 = 1 := by
  have h := E4_coeff 0
  simpa [qExpansion_coeff, E4] using h

theorem E4_hasSum {q : ℂ} (hq : ‖q‖ < 1) :
    HasSum (fun n : ℕ => (if n = 0 then (1 : ℂ) else
      240 * (ArithmeticFunction.sigma 3 n : ℂ)) * q^n) (E4 q) := by
  have h := UpperHalfPlane.hasSum_qExpansion_of_norm_lt (f := ModularForm.E (k := 4) (by norm_num))
    (by norm_num : (0 : ℝ) < 1)
    (SlashInvariantFormClass.periodic_comp_ofComplex _ one_mem_strictPeriods_SL)
    (holo _) (bdd_at_infty _) hq
  simpa only [E4_coeff, smul_eq_mul, E4] using h

/-- Absolute convergence of the actual divisor-sum series throughout the unit disc. -/
theorem sigma_series_summable {q : ℂ} (hq : ‖q‖ < 1) :
    Summable (fun n : ℕ => (ArithmeticFunction.sigma 3 n : ℂ) * q^n) := by
  apply Summable.of_norm_bounded
    (summable_norm_pow_mul_geometric_of_norm_lt_one 4 hq)
  intro n
  simp only [norm_mul, norm_pow, Complex.norm_natCast]
  gcongr
  exact_mod_cast ArithmeticFunction.sigma_le_pow_succ 3 n

/-- The actual normalized Eisenstein series is exactly the usual divisor
q-series, including the holomorphic value at the cusp q=0. -/
theorem E4_series {q : ℂ} (hq : ‖q‖ < 1) :
    E4 q = 1 + 240 * ∑' n : ℕ, (ArithmeticFunction.sigma 3 n : ℂ) * q^n := by
  have hs := (hasSum_ite_eq (α := ℂ) (0 : ℕ) 1).add
    ((sigma_series_summable hq).hasSum.mul_left (240 : ℂ))
  apply (E4_hasSum hq).unique
  convert hs using 1
  funext n
  by_cases hn : n = 0
  · subst n
    simp
  · simp [hn, mul_assoc]

/-- Exact fourth-moment majorant at radius 1/100, derived from the genuine
power-geometric summation formula rather than an assumed analytic bound. -/
theorem fourth_moment_hasSum :
    HasSum (fun n : ℕ => (n : ℝ)^4 * (1/100 : ℝ)^n)
      (37036700 / 3169966833 : ℝ) := by
  have h := hasSum_pow_mul_geometric_of_norm_lt_one 4
    (r := (1/100 : ℝ)) (by norm_num : ‖(1/100 : ℝ)‖ < 1)
  norm_num [Finset.sum_range_succ, Nat.stirlingSecond_succ_succ, Nat.factorial_succ] at h ⊢
  exact h

/-- Uniform small-disc bound on the actual normalized Eisenstein series.
The coefficient estimate used is sigma_3(n)<=n^4, not the false bound n^3. -/
theorem E4_bound {q : ℂ} (hq : ‖q‖ ≤ 1/100) : ‖E4 q‖ < 4 := by
  have hq' : ‖q‖ < 1 := lt_of_le_of_lt hq (by norm_num)
  have hg := (hasSum_ite_eq (α := ℝ) (0 : ℕ) 1).add
    (fourth_moment_hasSum.mul_left (240 : ℝ))
  have hb := (E4_hasSum hq').norm_le_of_bounded hg (fun n => ?_)
  · norm_num at hb
    linarith
  · by_cases hn : n = 0
    · subst n
      norm_num
    · simp only [hn, ite_false, norm_mul, norm_pow,
        norm_natCast, Complex.norm_ofNat]
      have hs : (ArithmeticFunction.sigma 3 n : ℝ) ≤ (n : ℝ)^4 := by
        exact_mod_cast ArithmeticFunction.sigma_le_pow_succ 3 n
      have hp : ‖q‖^n ≤ (1/100 : ℝ)^n := pow_le_pow_left₀ (norm_nonneg _) hq n
      nlinarith [mul_le_mul hs hp (by positivity) (by positivity)]

end E4Producer318
