module
public import WeierstrassImmersion318
public section
noncomputable section
open Filter Set
open scoped Topology
namespace AnalyticODEUniqueness318
set_option maxHeartbeats 0

lemma germ_eq_of_derivatives {f g : ℂ → ℂ} {z : ℂ}
    (hf : AnalyticAt ℂ f z) (hg : AnalyticAt ℂ g z)
    (h : ∀ n, iteratedDeriv n f z = iteratedDeriv n g z) : f =ᶠ[𝓝 z] g := by
  have hh : analyticOrderAt (fun w => f w - g w) z = ⊤ := by
    rw [ENat.eq_top_iff_forall_ge]
    intro n
    have hsub : AnalyticAt ℂ (fun w => f w - g w) z := hf.sub hg
    rw [natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hsub]
    intro i hi
    rw [iteratedDeriv_fun_sub hf.contDiffAt hg.contDiffAt, h i, sub_self]
  filter_upwards [analyticOrderAt_eq_top.mp hh] with w hw
  exact sub_eq_zero.mp hw

/-- Analytic uniqueness for the actual autonomous quadratic second-order ODE.
The ODE hypotheses are neighborhood equalities, not only equalities at the initial point. -/
theorem quadratic_germ_unique {f g : ℂ → ℂ} {z a b : ℂ}
    (hf : AnalyticAt ℂ f z) (hg : AnalyticAt ℂ g z)
    (hF : deriv (deriv f) =ᶠ[𝓝 z] (fun w => a * (f w * f w) + b))
    (hG : deriv (deriv g) =ᶠ[𝓝 z] (fun w => a * (g w * g w) + b))
    (h0 : f z = g z) (h1 : deriv f z = deriv g z) : f =ᶠ[𝓝 z] g := by
  apply germ_eq_of_derivatives hf hg
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simpa using h0
    | succ n =>
      cases n with
      | zero => simpa using h1
      | succ n =>
        have hf2 := hF.iteratedDeriv_eq n
        have hg2 := hG.iteratedDeriv_eq n
        rw [← iteratedDeriv_succ', ← iteratedDeriv_succ'] at hf2 hg2
        rw [hf2, hg2]
        have hff : AnalyticAt ℂ (fun w => f w * f w) z := hf.mul hf
        have hgg : AnalyticAt ℂ (fun w => g w * g w) z := hg.mul hg
        have haff : AnalyticAt ℂ (fun w => a * (f w * f w)) z := by fun_prop
        have hagg : AnalyticAt ℂ (fun w => a * (g w * g w)) z := by fun_prop
        rw [iteratedDeriv_fun_add haff.contDiffAt
          (analyticAt_const.contDiffAt),
          iteratedDeriv_fun_add hagg.contDiffAt
          (analyticAt_const.contDiffAt),
          iteratedDeriv_const_mul a hff.contDiffAt,
          iteratedDeriv_const_mul a hgg.contDiffAt,
          iteratedDeriv_fun_mul hf.contDiffAt hf.contDiffAt,
          iteratedDeriv_fun_mul hg.contDiffAt hg.contDiffAt]
        congr 2
        apply Finset.sum_congr rfl
        intro i hi
        rw [ih i (by have := Finset.mem_range.mp hi; omega),
          ih (n-i) (by omega)]
end AnalyticODEUniqueness318
