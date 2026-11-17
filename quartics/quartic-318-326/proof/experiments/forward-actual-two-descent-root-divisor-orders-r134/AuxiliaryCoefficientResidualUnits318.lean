module
public import Mathlib.Data.Nat.Squarefree
public import Mathlib.Tactic
public section
namespace AuxiliaryCoefficientResidualUnits318

/-- A displayed prime factor of the signed squarefree coefficient occurs
exactly once. The residual unit is a conclusion, not a local input. -/
theorem residual_unit (C D : ℤ) (hs : Squarefree C)
    (p : ℕ) (hp : p.Prime) (he : C=(p:ℤ)*D) : ¬(p:ℤ)∣D := by
  rintro ⟨k,hk⟩
  apply (Int.squarefree_iff_prime_sq_not_dvd.mp hs p hp)
  refine ⟨k,?_⟩
  rw [he,hk]
  ring

/-- Split off any selected factor p of P. Both R=P/p and the complementary
factor U are automatically units at p, by squarefreeness of C. -/
theorem selected_residuals (C ε : ℤ) (P U : ℕ) (hs : Squarefree C)
    (he : C=ε*(P:ℤ)*(U:ℤ)) (p : ℕ) (hp : p.Prime) (hd : p∣P) :
    ∃ R : ℕ, P=p*R ∧ ¬(p:ℤ)∣ε*(R:ℤ)*(U:ℤ) ∧
      ¬p∣R ∧ ¬p∣U := by
  obtain ⟨R,hR⟩ := hd
  have hfac : C=(p:ℤ)*(ε*(R:ℤ)*(U:ℤ)) := by
    rw [he,hR]
    push_cast
    ring
  have hunit := residual_unit C (ε*(R:ℤ)*(U:ℤ)) hs p hp hfac
  refine ⟨R,hR,hunit,?_,?_⟩
  · intro hdR
    have hz : (p:ℤ)∣(R:ℤ) := by exact_mod_cast hdR
    exact hunit (dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hz ε) (U:ℤ))
  · intro hdU
    have hz : (p:ℤ)∣(U:ℤ) := by exact_mod_cast hdU
    exact hunit (dvd_mul_of_dvd_right hz (ε*(R:ℤ)))

/-- Excluding the auxiliary prime from the coefficient support excludes it
at each individual coefficient prime, without an extra unit assumption. -/
theorem new_prime_unit (C : ℤ) (p q : ℕ) (hp : p.Prime) (hq : q.Prime)
    (hpC : (p:ℤ)∣C) (hqC : ¬(q:ℤ)∣C) : ¬(p:ℤ)∣(q:ℤ) := by
  intro hd
  have hn : p∣q := by exact_mod_cast hd
  have he : p=q := ((Nat.dvd_prime hq).mp hn).resolve_left hp.ne_one
  exact hqC (he ▸ hpC)

/-- The actual support exclusion suffices for the preceding unit result;
nondivisibility of q in C need not be supplied separately. -/
theorem new_prime_unit_of_support (C : ℤ) (hC0 : C≠0)
    (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hpC : (p:ℤ)∣C)
    (hqS : q∉insert 2 (insert 3 C.natAbs.primeFactors)) :
    ¬(p:ℤ)∣(q:ℤ) := by
  apply new_prime_unit C p q hp hq hpC
  intro hd
  have hn : q∣C.natAbs := by
    simpa using (Int.natAbs_dvd_natAbs.mpr hd)
  have hm : q∈C.natAbs.primeFactors :=
    Nat.mem_primeFactors.mpr ⟨hq,hn,Int.natAbs_ne_zero.mpr hC0⟩
  exact hqS (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))

/-- At an actual coefficient prime, C=1 modulo24 supplies the missing
unit6 condition used by both local character identities. -/
theorem six_unit (C : ℤ) (hC : C%24=1) (p : ℕ) (hp : p.Prime)
    (hpC : (p:ℤ)∣C) : ¬(p:ℤ)∣6 := by
  intro hd
  have hn : p∣(6:ℕ) := by exact_mod_cast hd
  have hm : p∣2*3 := by simpa using hn
  rcases hp.dvd_mul.mp hm with h2 | h3
  · have he : p=2 := ((Nat.dvd_prime Nat.prime_two).mp h2).resolve_left hp.ne_one
    subst p
    have hz := Int.dvd_iff_emod_eq_zero.mp hpC
    omega
  · have he : p=3 := ((Nat.dvd_prime (by decide : Nat.Prime 3)).mp h3).resolve_left hp.ne_one
    subst p
    have hz := Int.dvd_iff_emod_eq_zero.mp hpC
    omega

end AuxiliaryCoefficientResidualUnits318
