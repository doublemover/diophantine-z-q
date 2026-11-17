module
public import ActualTwoDescentGoodPrimeValuations318
public section
noncomputable section
namespace ActualTwoDescentCloseSquare318
open ActualTwoDescentHenselSquare318
set_option maxHeartbeats 16000000
variable {p : ℕ} [Fact p.Prime]

/-- Every actual p-adic value sufficiently close to1 has a nonzero square
root at odd p. This is proved in the completed field, not just for integers. -/
theorem actual_close_one_square (hp2 : p ≠ 2) (a : ℚ_[p]) (ha : ‖a-1‖ < 1) :
    ∃ r : ℚ_[p], r ≠ 0 ∧ r^2=a := by
  have hbound : ‖a‖ ≤ 1 := calc
    ‖a‖=‖(a-1)+1‖ := by congr 1; ring
    _ ≤ max ‖a-1‖ ‖(1 : ℚ_[p])‖ := Padic.nonarchimedean _ _
    _ ≤ 1 := max_le ha.le (by simp)
  let A : ℤ_[p] := ⟨a,hbound⟩
  have h2 : ‖(2 : ℤ_[p])‖=1 :=
    PadicInt.norm_natCast_eq_one_iff.mpr
      ((Nat.coprime_primes Fact.out (by decide : Nat.Prime 2)).mpr hp2)
  have hh : ‖(1 : ℤ_[p])^2-A‖ < ‖2*(1 : ℤ_[p])‖^2 := by
    rw [one_pow,mul_one,h2,one_pow]
    change ‖(1 : ℚ_[p])-a‖ < 1
    rwa [norm_sub_rev]
  obtain ⟨r,hr⟩ := actual_hensel_square A 1 hh
  have he : (r : ℚ_[p])^2=a := by exact_mod_cast hr
  refine ⟨(r : ℚ_[p]),?_,he⟩
  intro hz
  have ha0 : a=0 := by simpa only [hz,zero_pow (by decide : (2 : ℕ) ≠ 0)] using he.symm
  simpa [ha0] using ha

lemma actual_small_ratio (x y : ℚ_[p]) (hx : x ≠ 0) (hy : y ≠ 0)
    (h : y.valuation < x.valuation) : ‖x/y‖ < 1 := by
  rw [norm_div,div_lt_one (norm_pos_iff.mpr hy),Padic.norm_eq_zpow_neg_valuation hx,
    Padic.norm_eq_zpow_neg_valuation hy]
  exact (zpow_lt_zpow_iff_right₀ (by exact_mod_cast (Fact.out : p.Prime).one_lt)).mpr (neg_lt_neg h)

/-- A ratio1+x/y is genuinely square whenever its error has positive
valuation. This is the local near-torsion construction used next. -/
theorem actual_one_add_ratio_square (hp2 : p ≠ 2) (x y : ℚ_[p])
    (hx : x ≠ 0) (hy : y ≠ 0) (h : y.valuation < x.valuation) :
    ∃ r : ℚ_[p], r ≠ 0 ∧ r^2=1+x/y := by
  apply actual_close_one_square hp2
  simpa only [add_sub_cancel_left] using actual_small_ratio x y hx hy h

end ActualTwoDescentCloseSquare318
