module
public import AuxiliaryLocalUnitClass318
public import AuxiliaryDyadicValue318
public section
namespace AuxiliarySelectedDyadicBound318
open scoped BigOperators
local instance : Fact (Nat.Prime 2) := ⟨by decide⟩

/-- This bound concerns the newly constructed selected integer, not an
arbitrary locally represented value. The complementary prime product and
the new prime are units at2, so its valuation is literally alpha(2). -/
theorem selected_valuation (S : Finset ℕ) (α : ℕ → ℕ)
    (hS : ∀ p∈S,p.Prime) (h2 : 2∈S)
    (σ : ℤ) (hσ : σ=1 ∨ σ= -1) (q : ℕ) (hq : q.Prime) (hqS : q∉S) :
    let t : ℤ := σ*((∏ p∈S,p^α p):ℕ)*(q:ℤ)
    (t:ℚ_[2]).valuation=(α 2:ℤ) ∧
      ∃ v : ℤ, Odd v ∧ t=2^α 2*v := by
  classical
  let R : ℕ := ∏ p∈S.erase 2,p^α p
  let v : ℤ := σ*(R:ℤ)*(q:ℤ)
  have hR := (AuxiliaryLocalUnitClass318.prime_product_complement S α hS 2 h2).1
  have hE : ¬(2:ℤ)∣σ*(R:ℤ) :=
    AuxiliaryLocalUnitClass318.signed_complement_unit S α hS 2 h2 σ hσ
  have hq2 : q≠2 := by
    intro he
    exact hqS (he.symm ▸ h2)
  have hqN : ¬2∣q := by
    intro hd
    have he := ((Nat.dvd_prime hq).mp hd).resolve_left (by decide : (2:ℕ)≠1)
    exact hq2 he.symm
  have hqZ : ¬(2:ℤ)∣(q:ℤ) := by exact_mod_cast hqN
  have hvunit : ¬(2:ℤ)∣v := by
    intro hd
    rcases (Nat.prime_iff_prime_int.mp Nat.prime_two).dvd_mul.mp hd with h | h
    · exact hE h
    · exact hqZ h
  have hvodd : Odd v := by
    apply Int.odd_iff.mpr
    have hn := Int.emod_nonneg v (by decide : (2:ℤ)≠0)
    have hl := Int.emod_lt_of_pos v (by decide : (0:ℤ)<2)
    have hz : v%2≠0 := fun h => hvunit (Int.dvd_iff_emod_eq_zero.mpr h)
    omega
  have he : σ*((∏ p∈S,p^α p):ℕ)*(q:ℤ)=2^α 2*v := by
    rw [hR]
    dsimp only [R,v]
    push_cast
    ring
  have hv0 : v≠0 := by
    intro h
    exact hvunit (by simp [h])
  have hvQ : (v:ℚ_[2])≠0 := by exact_mod_cast hv0
  have heQ : ((σ*((∏ p∈S,p^α p):ℕ)*(q:ℤ):ℤ):ℚ_[2])=
      (2:ℚ_[2])^α 2*(v:ℚ_[2]) := by exact_mod_cast he
  have hpval : (2:ℚ_[2]).valuation=1 := by
    simpa using (Padic.valuation_p (p:=2))
  refine ⟨?_,v,hvodd,he⟩
  rw [heQ,Padic.valuation_mul (pow_ne_zero _ (by norm_num : (2:ℚ_[2])≠0)) hvQ,
    Padic.valuation_pow,hpval,Padic.valuation_intCast,
    padicValInt.eq_zero_of_not_dvd hvunit] <;> simp

/-- Named local block: the selected value has valuation at most1. In the
odd branch it is1 modulo8; in the even branch its literal integer half is7
modulo8. The latter uses the checked mod16-before-division theorem. -/
theorem selected_bound_and_half_residue (C : ℤ) (hC : C%8=1)
    (S : Finset ℕ) (α : ℕ → ℕ) (hS : ∀ p∈S,p.Prime) (h2 : 2∈S)
    (ha : α 2≤1) (σ : ℤ) (hσ : σ=1 ∨ σ= -1)
    (q : ℕ) (hq : q.Prime) (hqS : q∉S)
    (X Z T Y : ℚ_[2])
    (hA : X^2-2*Z^2=((σ*((∏ p∈S,p^α p):ℕ)*(q:ℤ):ℤ):ℚ_[2]))
    (hB : (C:ℚ_[2])*T^2-6*Y^2=((σ*((∏ p∈S,p^α p):ℕ)*(q:ℤ):ℤ):ℚ_[2])) :
    let t : ℤ := σ*((∏ p∈S,p^α p):ℕ)*(q:ℤ)
    (t:ℚ_[2]).valuation=(α 2:ℤ) ∧ (t:ℚ_[2]).valuation≤1 ∧
      (α 2=0 → Odd t ∧ t%8=1) ∧
      (α 2=1 → Odd (t/2) ∧ (t/2)%8=7) := by
  dsimp only
  obtain ⟨hval,v,hv,he⟩ := selected_valuation S α hS h2 σ hσ q hq hqS
  refine ⟨hval,?_,?_,?_⟩
  · rw [hval]
    exact_mod_cast ha
  · intro h0
    have het : σ*((∏ p∈S,p^α p):ℕ)*(q:ℤ)=v := by simpa [h0] using he
    rw [het] at hA hB ⊢
    exact ⟨hv,AuxiliaryDyadicValue318.unit_common_value C v hC hv X Z T Y hA hB⟩
  · intro h1
    have het : σ*((∏ p∈S,p^α p):ℕ)*(q:ℤ)=2*v := by simpa [h1] using he
    have hdiv : (σ*((∏ p∈S,p^α p):ℕ)*(q:ℤ))/2=v := by omega
    rw [hdiv]
    rw [het] at hA hB
    exact ⟨hv,AuxiliaryDyadicValue318.even_common_value C v hC hv X Z T Y hA hB⟩

end AuxiliarySelectedDyadicBound318
