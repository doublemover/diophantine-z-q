module
public import ActualTwoDescentProducedSupportImages318
public import Mathlib.Algebra.Order.Archimedean.Basic
public section
noncomputable section
namespace ActualTwoDescentUniformLocalSquare318
open ActualTwoDescentHenselSquare318
set_option maxHeartbeats 16000000
variable {p : ℕ} [Fact p.Prime]

/-- A uniform completed-field square-root neighborhood valid ALSO at2.
The constant1/4 is a lower bound for the squared derivative norm. -/
theorem actual_quarter_square (a : ℚ_[p]) (ha : ‖a-1‖ < (1/4 : ℝ)) :
    ∃ r : ℚ_[p], r ≠ 0 ∧ r^2=a := by
  have hbound : ‖a‖ ≤ 1 := calc
    ‖a‖=‖(a-1)+1‖ := by congr 1; ring
    _ ≤ max ‖a-1‖ ‖(1 : ℚ_[p])‖ := Padic.nonarchimedean _ _
    _ ≤ 1 := max_le (by linarith) (by simp)
  let A : ℤ_[p] := ⟨a,hbound⟩
  have h2 : (1/4 : ℝ) ≤ ‖(2 : ℤ_[p])‖^2 := by
    by_cases hp : p=2
    · subst p
      rw [PadicInt.norm_p]
      norm_num
    · have hunit : ‖(2 : ℤ_[p])‖=1 := PadicInt.norm_natCast_eq_one_iff.mpr
        ((Nat.coprime_primes Fact.out (by decide : Nat.Prime 2)).mpr hp)
      rw [hunit]
      norm_num
  have hh : ‖(1 : ℤ_[p])^2-A‖ < ‖2*(1 : ℤ_[p])‖^2 := by
    rw [one_pow,mul_one]
    have he : ‖(1 : ℤ_[p])-A‖=‖a-1‖ := by
      change ‖(1 : ℚ_[p])-a‖=‖a-1‖
      exact norm_sub_rev _ _
    rw [he]
    exact lt_of_lt_of_le ha h2
  obtain ⟨r,hr⟩ := actual_hensel_square A 1 hh
  have he : (r : ℚ_[p])^2=a := by exact_mod_cast hr
  refine ⟨(r : ℚ_[p]),?_,he⟩
  intro hz
  have ha0 : a=0 := by simpa only [hz,zero_pow (by decide : (2 : ℕ) ≠ 0)] using he.symm
  norm_num [ha0] at ha

/-- A nonzero square can be made arbitrarily small in every Q_p. The
actual witness is a power of the same prime, chosen by a real power bound. -/
theorem actual_small_local_square (ε : ℝ) (hε : 0 < ε) :
    ∃ b : ℚ_[p], b ≠ 0 ∧ ‖b^2‖ < ε := by
  have hbase : ‖(p : ℚ_[p])‖^2 < 1 :=
    pow_lt_one₀ (norm_nonneg _) Padic.norm_p_lt_one (by decide)
  obtain ⟨k,hk⟩ := exists_pow_lt_of_lt_one hε hbase
  refine ⟨(p : ℚ_[p])^k,pow_ne_zero _ (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero),?_⟩
  convert hk using 1
  rw [norm_pow,norm_pow,←pow_mul,←pow_mul,Nat.mul_comm]

end ActualTwoDescentUniformLocalSquare318
