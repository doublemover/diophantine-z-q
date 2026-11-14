module
public import ActualTwoDescentComplementMonomial318
public section
noncomputable section
namespace ActualTwoDescentFourTwoAdicClasses318
open ActualTwoDescentComplementMonomial318 ActualTwoDescentPrimeMonomials318
open ActualTwoDescentZeroSumCompletion318 ActualTwoDescentLocalKummerWitness318
open ActualTwoDescentTwoAdicSquare318
open scoped BigOperators
set_option maxHeartbeats 16000000

/-- All four surviving normalized classes have ACTUAL Q2 curve witnesses.
The fourth class is the complementary literal prime product; its multiplier
is the reciprocal of the actual beta square root, not a formal F2 symbol. -/
theorem actual_four_two_adic_classes {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → ℕ) [∀ i, Fact (p i).Prime] (b : ι → ZMod 2)
    (hb : (monomial p b : ZMod 8)=1) (c e : ZMod 2) :
    Nonempty (LocalKummerPoint (p:=2) (monomial p (c • ones ι+e • b)) (∏ i, p i)) := by
  have hn0 : (∏ i, p i) ≠ 0 := Finset.prod_ne_zero_iff.mpr
    (fun i _ => (Fact.out : (p i).Prime).ne_zero)
  obtain ⟨r,hr⟩ := actual_two_adic_square (monomial p b) hb
  have hr0 : r ≠ 0 := by
    intro he
    rw [he,zero_pow (by decide : (2 : ℕ) ≠ 0)] at hr
    exact (Nat.cast_ne_zero.mpr (monomial_pos p b).ne') hr.symm
  have hbase : Nonempty (LocalKummerPoint (p:=2) (monomial p b) (∏ i, p i)) :=
    actual_local_kummer_of_square _ _ r hr0 hr
  have hcomp : Nonempty (LocalKummerPoint (p:=2) (monomial p (ones ι+b)) (∏ i, p i)) := by
    apply actual_local_kummer_of_first_torsion _ _ hn0 r⁻¹ (inv_ne_zero hr0)
    have he : (monomial p (ones ι+b) : ℚ_[2])*(monomial p b : ℚ_[2])=(∏ i, p i : ℕ) := by
      exact_mod_cast actual_complement_product p b
    rw [inv_pow,hr]
    field_simp [(Nat.cast_ne_zero.mpr (monomial_pos p b).ne' : (monomial p b : ℚ_[2]) ≠ 0)]
    exact he
  fin_cases c <;> fin_cases e
  · simpa only [zero_smul,add_zero,actual_zero_monomial] using
      actual_local_kummer_of_square (p:=2) 1 (∏ i, p i) 1 one_ne_zero (by norm_num)
  · simpa only [zero_smul,one_smul,zero_add] using hbase
  · simpa only [one_smul,zero_smul,add_zero,actual_one_monomial] using
      actual_local_kummer_of_first_torsion (p:=2) (∏ i, p i) (∏ i, p i) hn0 1 one_ne_zero (by simp)
  · simpa only [one_smul] using hcomp

end ActualTwoDescentFourTwoAdicClasses318
