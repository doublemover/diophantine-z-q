module
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.Tactic
public section
namespace PadicSquareNormalization318

/-- Every actual nonzero p-adic value has an explicit unit times a parity
power of p, up to a nonzero square. Negative valuations are included. -/
theorem parity_unit (p : ℕ) [Fact p.Prime] (t : ℚ_[p]) (ht : t≠0) :
    ∃ (α : ℤ) (u : ℤ_[p]) (s : ℚ_[p]),
      (α=0 ∨ α=1) ∧ ‖u‖=1 ∧ s≠0 ∧ t=((p:ℚ_[p])^α*(u:ℚ_[p]))*s^2 := by
  have hp : p.Prime := Fact.out
  have hpQ : (p:ℚ_[p])≠0 := by exact_mod_cast hp.ne_zero
  have hpR : (p:ℝ)≠0 := by exact_mod_cast hp.ne_zero
  let v : ℤ := t.valuation
  let α : ℤ := v%2
  let e : ℤ := v/2
  have hunit : ‖t*(p:ℚ_[p])^(-v)‖=1 := by
    rw [norm_mul,Padic.norm_eq_zpow_neg_valuation ht,Padic.norm_p_zpow,neg_neg]
    change (p:ℝ)^(-v)*(p:ℝ)^v=1
    rw [←zpow_add₀ hpR]
    simp
  let u : ℤ_[p] := ⟨t*(p:ℚ_[p])^(-v),le_of_eq hunit⟩
  let s : ℚ_[p] := (p:ℚ_[p])^e
  have hα : α=0 ∨ α=1 := by
    have hlo := Int.emod_nonneg v (by norm_num : (2:ℤ)≠0)
    have hhi := Int.emod_lt_of_pos v (by norm_num : (0:ℤ)<2)
    dsimp only [α]
    omega
  have hexp : α + -v + (e+e)=0 := by dsimp only [α,e]; omega
  refine ⟨α,u,s,hα,?_,zpow_ne_zero _ hpQ,?_⟩
  · exact hunit
  · symm
    calc
      ((p:ℚ_[p])^α*(u:ℚ_[p]))*s^2 =
          t*(p:ℚ_[p])^(α + -v + (e+e)) := by
        dsimp only [u,s]
        rw [pow_two]
        simp only [zpow_add₀ hpQ]
        ring
      _=t := by rw [hexp,zpow_zero,mul_one]

/-- Dividing all four coordinates by the same nonzero square factor preserves
both binary representations of the normalized common value. -/
theorem normalize_common_value {K : Type*} [Field K]
    (C t v s x z y T : K) (hs : s≠0) (ht : t=v*s^2)
    (hA : x^2-2*z^2=t) (hB : C*T^2-6*y^2=t) :
    (x/s)^2-2*(z/s)^2=v ∧ C*(T/s)^2-6*(y/s)^2=v := by
  have hs2 : s^2≠0 := pow_ne_zero 2 hs
  constructor
  · calc
      (x/s)^2-2*(z/s)^2=(x^2-2*z^2)/s^2 := by ring
      _=v := by rw [hA,ht]; exact mul_div_cancel_right₀ v hs2
  · calc
      C*(T/s)^2-6*(y/s)^2=(C*T^2-6*y^2)/s^2 := by ring
      _=v := by rw [hB,ht]; exact mul_div_cancel_right₀ v hs2

end PadicSquareNormalization318
