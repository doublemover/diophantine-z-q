module
public import ActualOriginalLocalFactorConsumer318
public import Mathlib.Analysis.PSeries
public import Mathlib.Analysis.SpecialFunctions.Log.Summable
public section
noncomputable section
namespace ActualGoodPrimeDensityProduct318
open ActualLocalVolumeClosedForm318 ActualLocalPrimitiveNormalization318
open scoped BigOperators Topology
set_option maxHeartbeats 22000000

@[expose] def Good (κ : ℤ) (p : ℕ) : Prop := p.Prime ∧ p≠2 ∧ ¬(p:ℤ)∣κ
/-- Every included factor is the genuine original unrestricted local
density; excluded primes and nonprimes contribute the identity. -/
@[expose] def factor (κ : ℤ) (p : ℕ) : ℝ := by
  classical
  exact if Good κ p then (localFactor p:ℝ) else 1
lemma factor_pos (κ : ℤ) (p : ℕ) : 0<factor κ p := by
  classical
  unfold factor
  split_ifs with h
  · have hh : (1:ℝ)<(localFactor p:ℝ) := by exact_mod_cast actual_factor_gt_one p h.1
    linarith
  · norm_num
lemma actual_factor_error (κ : ℤ) (p : ℕ) : |factor κ p-1|≤1/(p:ℝ)^3 := by
  classical
  unfold factor
  split_ifs with h
  · have hh := actual_factor_tail_bound p h.1
    have hpos : (0:ℝ)<(localFactor p:ℝ)-1 := by exact_mod_cast hh.1
    rw [abs_of_pos hpos]
    exact_mod_cast hh.2
  · simp only [sub_self,abs_zero]
    positivity

theorem actual_good_prime_error_summable (κ : ℤ) :
    Summable (fun p : ℕ => |factor κ p-1|) := by
  have hs : Summable (fun p : ℕ => 1/(p:ℝ)^3) :=
    Real.summable_one_div_nat_pow.mpr (by norm_num)
  exact hs.of_nonneg_of_le (fun _ => abs_nonneg _) (actual_factor_error κ)

/-- A generic elementary analytic step, applied below only to exact
constructed original local factors. -/
theorem positive_product_of_error (f : ℕ → ℝ) (hf : ∀p,0<f p)
    (hs : Summable (fun p => |f p-1|)) : ∃C : ℝ,0<C ∧ HasProd f C := by
  have hn : Summable (fun p => ‖f p-1‖) := by simpa only [Real.norm_eq_abs] using hs
  have hh := Real.summable_log_one_add_of_summable hn.of_norm
  have he (x : ℝ) : 1+(x-1)=x := by ring
  have hlog : Summable (fun p => Real.log (f p)) := by simpa only [he] using hh
  exact ⟨Real.exp (∑'p,Real.log (f p)),Real.exp_pos _,Real.hasProd_of_hasSum_log hf hlog.hasSum⟩

/-- The good-prime part of the ACTUAL original singular series has a
strictly positive product, not merely formally convergent factors. -/
theorem actual_good_prime_positive_product (κ : ℤ) :
    ∃S : ℝ,0<S ∧ HasProd (factor κ) S :=
  positive_product_of_error (factor κ) (factor_pos κ) (actual_good_prime_error_summable κ)

end ActualGoodPrimeDensityProduct318
