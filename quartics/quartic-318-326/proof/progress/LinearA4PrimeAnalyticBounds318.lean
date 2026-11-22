module
public import LinearA4PrimeLogMoment318
public import Mathlib.Analysis.PSeries
public section
noncomputable section

namespace LinearA4PrimeAnalyticBounds318
open LinearA4PrimeLogMoment318
open scoped BigOperators

def squareBudget : ℝ := ∑' p : ℕ, 1/(p:ℝ)^2

/-- The square-error budget is uniform even for arbitrary finite sets of
indices, hence for all fixed-wheel prime windows and all single omissions. -/
theorem square_error_budget (S : Finset ℕ) :
    (∑ p ∈ S,1/(p:ℝ)^2) ≤ squareBudget := by
  unfold squareBudget
  exact Summable.sum_le_tsum S (fun _ _ => by positivity)
    (Real.summable_one_div_nat_pow.mpr (by decide : 1 < 2))

theorem density_majorant (p r : ℕ) (hp : p.Prime) (chi A g : ℝ)
    (hchi : chi≤1) (hA : 0≤A)
    (h : |g-((r:ℝ)+2*chi)/(p:ℝ)|≤A/(p:ℝ)^2) :
    g ≤ ((r:ℝ)+2+A)/(p:ℝ) := by
  have hp1 : 1≤(p:ℝ) := by exact_mod_cast hp.one_lt.le
  have hpp : 0<(p:ℝ) := zero_lt_one.trans_le hp1
  have hg := (abs_le.mp h).2
  have htt : (p:ℝ)≤(p:ℝ)^2 := by nlinarith [mul_nonneg hpp.le (sub_nonneg.mpr hp1)]
  calc
    g ≤ ((r:ℝ)+2*chi)/(p:ℝ)+A/(p:ℝ)^2 := by linarith
    _ ≤ ((r:ℝ)+2)/(p:ℝ)+A/(p:ℝ) := by
      exact add_le_add (div_le_div_of_nonneg_right (by linarith) hpp.le)
        (div_le_div_of_nonneg_left hA hpp htt)
    _ = ((r:ℝ)+2+A)/(p:ℝ) := by ring

/-- The actual rank-r Euler-factor expansion implies the finite prime
log-moment bound required by the truncated Selberg product. -/
theorem density_log_moment (S : Finset ℕ) (g chi : ℕ → ℝ) (y r : ℕ)
    (hy : 2≤y) (hS : S⊆Nat.primesLE y) (A : ℝ) (hA : 0≤A)
    (hchi : ∀ p∈S, chi p≤1)
    (h : ∀ p∈S, |g p-((r:ℝ)+2*chi p)/(p:ℝ)|≤A/(p:ℝ)^2) :
    (∑ p ∈ S,g p*Real.log (p:ℝ)) ≤
      (8*((r:ℝ)+2+A))*Real.log (y:ℝ) := by
  refine weighted_moment S g y hy hS ((r:ℝ)+2+A) (by positivity) ?_
  intro p hp
  exact density_majorant p r (Nat.mem_primesLE.mp (hS hp)).2 (chi p) A
    (g p) (hchi p hp) hA (h p hp)

end LinearA4PrimeAnalyticBounds318
