module
public import AuxiliaryActualFiniteValues318
public import AuxiliarySelectionCallerBridges318
public section
noncomputable section
namespace AuxiliaryActualSelectedValue318
open scoped BigOperators

/-- Choose the sign and the coefficient support before the prime. The
finite construction then supplies both local norm values on that fixed
support. Prime exclusion, nonzero selected value, real positivity and the
classification of all remaining bad primes are derived, not additional
selection hypotheses. No norm at the newly selected prime is assumed. -/
theorem select (C : ℤ) (hC : C≠0) (N : ℕ)
    (hlocal : ∀ p (hp : p∈insert 2 (insert 3 C.natAbs.primeFactors)),
      ∀ [Fact p.Prime], ∃ x z T y : ℚ_[p],
        ¬(x=0 ∧ z=0 ∧ T=0 ∧ y=0) ∧
        x^2-2*z^2=(C:ℚ_[p])*T^2-6*y^2) :
    ∃ (σ : ℤ) (α : ℕ → ℕ) (q : ℕ),
      (σ=1 ∨ σ= -1) ∧ C=σ*(C.natAbs:ℤ) ∧ (∀ p,α p≤1) ∧
      N<q ∧ q.Prime ∧ q∉insert 2 (insert 3 C.natAbs.primeFactors) ∧
      ¬(q:ℤ)∣6*C ∧
      let t : ℤ := σ*((∏ p∈insert 2 (insert 3 C.natAbs.primeFactors),p^α p):ℕ)*(q:ℤ)
      t≠0 ∧ (0:ℝ)<(t:ℝ)/(C:ℝ) ∧
      (∀ p (hp : p∈insert 2 (insert 3 C.natAbs.primeFactors)),
        ∀ [Fact p.Prime], ∃ X Z T Y : ℚ_[p],
          X^2-2*Z^2=(t:ℚ_[p]) ∧ (C:ℚ_[p])*T^2-6*Y^2=(t:ℚ_[p])) ∧
      (∀ (p : ℕ), p.Prime → (p:ℤ)∣(6*C)*(C*t) →
        p∈insert 2 (insert 3 C.natAbs.primeFactors) ∨ p=q) := by
  classical
  let S := insert 2 (insert 3 C.natAbs.primeFactors)
  have hS : ∀ p∈S,p.Prime := by
    intro p hp
    simp only [S,Finset.mem_insert] at hp
    rcases hp with rfl | rfl | hp
    · exact Nat.prime_two
    · decide
    · exact (Nat.mem_primeFactors.mp hp).1
  obtain ⟨σ,hσ,hCσ,hpositive⟩ :=
    AuxiliarySelectionCallerBridges318.real_sign_choice C hC
  have hloc : ∀ p (hp : p∈S), letI : Fact p.Prime := ⟨hS p hp⟩;
      ∃ x z T y : ℚ_[p], ¬(x=0 ∧ z=0 ∧ T=0 ∧ y=0) ∧
        x^2-2*z^2=(C:ℚ_[p])*T^2-6*y^2 := by
    intro p hp
    letI : Fact p.Prime := ⟨hS p hp⟩
    exact hlocal p hp
  obtain ⟨α,q,hα,hN,hq,hvalues⟩ :=
    AuxiliaryActualFiniteValues318.prime_with_actual_finite_values
      C hC S hS hloc σ hσ (N+∑ p∈S,p)
  obtain ⟨hqS,hqunit⟩ := AuxiliarySelectionCallerBridges318.new_prime_outside_and_unit
    C hC q N hq hN
  have hD := AuxiliarySelectionCallerBridges318.power_product_pos S α hS
  have hreal := hpositive (∏ p∈S,p^α p) q hD hq.pos
  have hne : σ*((∏ p∈S,p^α p):ℕ)*(q:ℤ)≠0 := by
    intro hz
    rw [hz] at hreal
    norm_num at hreal
  refine ⟨σ,α,q,hσ,hCσ,hα,by omega,hq,hqS,hqunit,hne,hreal,?_,?_⟩
  · intro p hp inst
    exact hvalues p hp
  · intro p hp hd
    exact AuxiliarySelectionCallerBridges318.bad_support C hC α σ hσ q hq p hp hd

end AuxiliaryActualSelectedValue318
