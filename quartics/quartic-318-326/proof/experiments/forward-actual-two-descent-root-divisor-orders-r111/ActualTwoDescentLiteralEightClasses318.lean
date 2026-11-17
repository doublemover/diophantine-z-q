module
public import ActualTwoDescentRationalClassBound318
public section
noncomputable section
namespace ActualTwoDescentLiteralEightClasses318
open ActualTwoDescentPrimeMonomials318 ActualTwoDescentComplementMonomial318
open ActualTwoDescentZeroSumCompletion318 ActualTwoDescentSignedRepresentativeTransport318
open scoped BigOperators
set_option maxHeartbeats 16000000
variable {U : Type*} [Fintype U] [DecidableEq U]

/-- The four binary monomials are the literal rational squareclasses
1,beta,n,n*beta. The complementary product uses the explicit multiplier
beta inverse, so no coefficient-vector equality is mistaken for equality
of integer representatives. -/
theorem actual_four_monomial_classes (p : Option U → ℕ) [∀ i, Fact (p i).Prime]
    (beta : Option U → ZMod 2) (c e : ZMod 2) :
    ∃ t : ℚ, t ≠ 0 ∧ (monomial p (c • ones (Option U)+e • beta) : ℚ)=
      ((∏ i, p i : ℕ) : ℚ)^c.val*(monomial p beta : ℚ)^e.val*t^2 := by
  have hβ : (monomial p beta : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (monomial_pos p beta).ne'
  fin_cases c <;> fin_cases e
  · refine ⟨1,one_ne_zero,?_⟩
    simp [actual_zero_monomial]
  · refine ⟨1,one_ne_zero,?_⟩
    simp
  · refine ⟨1,one_ne_zero,?_⟩
    simp [actual_one_monomial]
  · refine ⟨(monomial p beta : ℚ)⁻¹,inv_ne_zero hβ,?_⟩
    simp only [one_smul,ZMod.val_one,pow_one]
    have he : (monomial p (ones (Option U)+beta) : ℚ)*(monomial p beta : ℚ)=(∏ i, p i : ℕ) := by
      exact_mod_cast actual_complement_product p beta
    calc
      _=((∏ i, p i : ℕ) : ℚ)/(monomial p beta : ℚ) := (eq_div_iff hβ).mpr he
      _=((∏ i, p i : ℕ) : ℚ)*(monomial p beta : ℚ)*((monomial p beta : ℚ)⁻¹)^2 := by
        field_simp [hβ]
        <;> ring

lemma actual_second_torsion_representative (p : Option U → ℕ) (ε : ZMod 2) :
    (signedSecond p ε (ε • ones (Option U)) : ℚ)=(-((∏ i, p i : ℕ) : ℚ))^ε.val := by
  fin_cases ε <;> simp [signedSecond,actual_zero_monomial,actual_one_monomial]

end ActualTwoDescentLiteralEightClasses318
