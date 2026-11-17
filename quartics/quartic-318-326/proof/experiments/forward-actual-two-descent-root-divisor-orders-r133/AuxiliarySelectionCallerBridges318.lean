module
public import Mathlib.Data.Nat.Squarefree
public import Mathlib.Tactic
public section
namespace AuxiliarySelectionCallerBridges318
open scoped BigOperators

theorem outside_of_sum_bound (S : Finset ℕ) (q N : ℕ)
    (hq : N+∑ p∈S,p<q) : q∉S := by
  intro hm
  have hle : q≤∑ p∈S,p :=
    Finset.single_le_sum (fun p _ => Nat.zero_le p) hm
  omega

theorem coefficient_prime_mem (C : ℤ) (hC : C≠0) (p : ℕ)
    (hp : p.Prime) (hd : (p:ℤ)∣C) :
    p∈insert 2 (insert 3 C.natAbs.primeFactors) := by
  have hn : p∣C.natAbs := by simpa using Int.natAbs_dvd_natAbs.mpr hd
  exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
    (Nat.mem_primeFactors.mpr ⟨hp,hn,Int.natAbs_ne_zero.mpr hC⟩))

theorem six_prime_mem (C : ℤ) (p : ℕ) (hp : p.Prime) (hd : (p:ℤ)∣6) :
    p∈insert 2 (insert 3 C.natAbs.primeFactors) := by
  have hn : p∣2*3 := by exact_mod_cast hd
  rcases hp.dvd_mul.mp hn with h | h
  · have he : p=2 := ((Nat.dvd_prime Nat.prime_two).mp h).resolve_left hp.ne_one
    simp [he]
  · have he : p=3 := ((Nat.dvd_prime (by decide : Nat.Prime 3)).mp h).resolve_left hp.ne_one
    simp [he]

/-- Choosing the finite-prime construction above this explicit bound
excludes q from the actual support and makes6C a unit at q. -/
theorem new_prime_outside_and_unit (C : ℤ) (hC : C≠0) (q N : ℕ)
    (hq : q.Prime)
    (hbound : N+∑ p∈insert 2 (insert 3 C.natAbs.primeFactors),p<q) :
    q∉insert 2 (insert 3 C.natAbs.primeFactors) ∧ ¬(q:ℤ)∣6*C := by
  have hout := outside_of_sum_bound _ q N hbound
  refine ⟨hout,?_⟩
  intro hd
  rcases (Nat.prime_iff_prime_int.mp hq).dvd_mul.mp hd with h | h
  · exact hout (six_prime_mem C q hq h)
  · exact hout (coefficient_prime_mem C hC q hq h)

theorem power_product_pos (S : Finset ℕ) (α : ℕ → ℕ)
    (hS : ∀ p∈S,p.Prime) : 0<∏ p∈S,p^α p := by
  exact Finset.prod_pos (fun p hp => pow_pos (hS p hp).pos _)

/-- The real-compatible sign is chosen, not supplied as an extra positivity
assumption. The positive unsigned selected value may have either signed C. -/
theorem real_sign_choice (C : ℤ) (hC : C≠0) :
    ∃ σ : ℤ, (σ=1 ∨ σ= -1) ∧ C=σ*(C.natAbs:ℤ) ∧
      ∀ D q : ℕ, 0<D → 0<q →
        (((σ*(D:ℤ)*(q:ℤ):ℤ):ℝ)/(C:ℝ))>0 := by
  by_cases hpos : 0<C
  · have hCR : (0:ℝ)<(C:ℝ) := by exact_mod_cast hpos
    refine ⟨1,Or.inl rfl,?_,?_⟩
    · simp [Int.natCast_natAbs,abs_of_pos hpos]
    · intro D q hD hq
      have hDR : (0:ℝ)<(D:ℝ) := by exact_mod_cast hD
      have hqR : (0:ℝ)<(q:ℝ) := by exact_mod_cast hq
      push_cast
      simpa using div_pos (mul_pos hDR hqR) hCR
  · have hneg : C<0 := by omega
    have hCR : (C:ℝ)<0 := by exact_mod_cast hneg
    refine ⟨-1,Or.inr rfl,?_,?_⟩
    · simp [Int.natCast_natAbs,abs_of_neg hneg]
    · intro D q hD hq
      have hDR : (0:ℝ)<(D:ℝ) := by exact_mod_cast hD
      have hqR : (0:ℝ)<(q:ℝ) := by exact_mod_cast hq
      have ht : ((-1:ℝ)*(D:ℝ)*(q:ℝ))<0 := by nlinarith [mul_pos hDR hqR]
      simpa only [Int.cast_mul,Int.cast_neg,Int.cast_one,Int.cast_natCast] using
        div_pos_of_neg_of_neg ht hCR

/-- The chosen real sign also supplies the exact signed-reciprocity branch.
Use epsilon=sigma; no unrelated sign choice is passed to the character product. -/
theorem character_sign_compatibility (C : ℤ) (hC : C%24=1) (N : ℕ)
    (σ : ℤ) (hσ : σ=1 ∨ σ= -1) (he : C=σ*(N:ℤ)) :
    (σ=1 ∧ N%4=1) ∨ (σ= -1 ∧ N%4=3 ∧ σ= -1) := by
  rcases hσ with rfl | rfl
  · have he' : C=(N:ℤ) := by simpa using he
    have hn : (N:ℤ)%4=1 := by rw [←he']; omega
    exact Or.inl ⟨rfl,by exact_mod_cast hn⟩
  · have he' : C= -(N:ℤ) := by simpa using he
    have hn : (N:ℤ)%4=3 := by rw [he'] at hC; omega
    exact Or.inr ⟨rfl,by exact_mod_cast hn,rfl⟩

private theorem prime_mem_of_dvd_product (S : Finset ℕ) (α : ℕ → ℕ)
    (hS : ∀ r∈S,r.Prime) (p : ℕ) (hp : p.Prime)
    (hd : p∣∏ r∈S,r^α r) : p∈S := by
  obtain ⟨r,hr,hdpow⟩ := (hp.prime.dvd_finsetProd_iff _).mp hd
  have hdr : p∣r := hp.dvd_of_dvd_pow hdpow
  have he : p=r := ((Nat.dvd_prime (hS r hr)).mp hdr).resolve_left hp.ne_one
  exact he.symm ▸ hr

/-- Every potentially bad prime for the selected B ternary is either an
original finite-support prime or the newly selected q. No support-divisor
classification is supplied as an extra input. -/
theorem bad_support (C : ℤ) (hC : C≠0) (α : ℕ → ℕ)
    (σ : ℤ) (hσ : σ=1 ∨ σ= -1) (q : ℕ) (hq : q.Prime)
    (p : ℕ) (hp : p.Prime)
    (hd : (p:ℤ)∣(6*C)*(C*(σ*((∏ r∈insert 2 (insert 3 C.natAbs.primeFactors),r^α r):ℕ)*(q:ℤ)))) :
    p∈insert 2 (insert 3 C.natAbs.primeFactors) ∨ p=q := by
  have hS : ∀ r∈insert 2 (insert 3 C.natAbs.primeFactors),r.Prime := by
    intro r hr
    simp only [Finset.mem_insert] at hr
    rcases hr with rfl | rfl | hr
    · exact Nat.prime_two
    · decide
    · exact (Nat.mem_primeFactors.mp hr).1
  have hpi := Nat.prime_iff_prime_int.mp hp
  rcases hpi.dvd_mul.mp hd with h | h
  · rcases hpi.dvd_mul.mp h with h6 | hC'
    · exact Or.inl (six_prime_mem C p hp h6)
    · exact Or.inl (coefficient_prime_mem C hC p hp hC')
  · rcases hpi.dvd_mul.mp h with hC' | ht
    · exact Or.inl (coefficient_prime_mem C hC p hp hC')
    · rcases hpi.dvd_mul.mp ht with hD | hq'
      · rcases hpi.dvd_mul.mp hD with hs | hprod
        · have hz : (p:ℤ)∣1 := by
            rcases hσ with rfl | rfl <;> simpa using hs
          have hn : p∣1 := by exact_mod_cast hz
          exact False.elim (hp.ne_one (Nat.dvd_one.mp hn))
        · have hn : p∣∏ r∈insert 2 (insert 3 C.natAbs.primeFactors),r^α r := by
            exact_mod_cast hprod
          exact Or.inl (prime_mem_of_dvd_product _ α hS p hp hn)
      · have hn : p∣q := by exact_mod_cast hq'
        exact Or.inr (((Nat.dvd_prime hq).mp hn).resolve_left hp.ne_one)

end AuxiliarySelectionCallerBridges318
