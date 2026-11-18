module
public import ScalarTwoThreePreparation318
public section
noncomputable section
namespace UniversalDyadicGuard318
open CoherentMultipleCharts318
local instance : Fact (Nat.Prime 2) := ⟨by norm_num⟩

private def tr (k : ℤ) : ℚ := ((chartU k)^2).re

private lemma tr_zero : tr 0 = 0 := by simp [tr, chartU_zero]

private lemma tr_ne {k : ℤ} (hk : k ≠ 0) : tr k ≠ 0 :=
  ScalarPackedLocalUnit318.half_trace_ne _ (ScalarTwoThreePreparation318.common_norm_ne k hk)

private lemma tr_value {k : ℤ} (hk : k ≠ 0) :
    padicValRat 2 (tr k) = 3 + 2 * (padicValInt 2 k : ℤ) := by
  unfold tr
  rw [ScalarHalfTraceDepth318.half_trace_two _ (ScalarTwoThreePreparation318.common_norm_ne k hk),
    ScalarIndexValuations318.chart_norm_two k hk]

private lemma one_le_val {k : ℤ} (hk : k ≠ 0) (hd : 2 ∣ k) : 1 ≤ padicValInt 2 k := by
  have h : ((2 : ℕ) : ℤ)^1 ∣ k := by simpa using hd
  exact ((padicValInt_dvd_iff (p := 2) 1 k).mp h).resolve_left hk

private lemma adjacent_val_ne {h : ℤ} (h0 : h ≠ 0) (h1 : h - 1 ≠ 0) :
    padicValInt 2 (h-1) ≠ padicValInt 2 h := by
  by_cases hd : 2 ∣ h
  · have hn : ¬ (2:ℤ) ∣ h-1 := by omega
    have hz := padicValInt.eq_zero_of_not_dvd (p := 2) hn
    have hp := one_le_val h0 hd
    omega
  · have hn : (2:ℤ) ∣ h-1 := by omega
    have hz := padicValInt.eq_zero_of_not_dvd (p := 2) hd
    have hp := one_le_val h1 hn
    omega

private lemma tr_difference {j : ℤ} (hj : j ≠ 0) (h : ℤ) :
    tr (j*(h-1)) - tr (j*h) ≠ 0 := by
  by_cases h0 : h = 0
  · subst h
    simpa [tr_zero] using (tr_ne (neg_ne_zero.mpr hj))
  by_cases h1 : h = 1
  · subst h
    simpa [tr_zero] using (neg_ne_zero.mpr (tr_ne hj))
  have hh : h-1 ≠ 0 := by omega
  intro he
  have hv := congrArg (padicValRat 2) (sub_eq_zero.mp he)
  rw [tr_value (mul_ne_zero hj hh), tr_value (mul_ne_zero hj h0),
    padicValInt.mul hj hh, padicValInt.mul hj h0] at hv
  have hdiff := adjacent_val_ne h0 hh
  omega

/-- All four rational trace guards on the true integer orbit are automatic. -/
theorem guards (ns : Fin 4 → ℤ) (hn : ∀ j, ns j ≠ 0) (h : ℤ) :
    RealGuardWitness318.Guards (CoherentMultiplePrefix318.u ns h) := by
  intro j
  simpa [RealGuardWitness318.denominator, CoherentMultiplePrefix318.u,
    CoherentMultiplePrefix318.parameters, tr] using tr_difference (hn j) h

/-- Consumer-facing substitute for the four prior nonzero-guard hypotheses. -/
theorem guard_values (ns : Fin 4 → ℤ) (hn : ∀ j, ns j ≠ 0) (h : ℤ) :
    ∀ j, RealGuardTrace318.guardValue (ns j) (h • LocalGenerator318.P) ≠ 0 :=
  (CoherentMultiplePrefix318.guards_iff ns h).mp (guards ns hn h)

end UniversalDyadicGuard318
