module
public import RationalContactPoint318
public import SourceTwistArithmetic318
public import ContactPrimeLimits318
public section
noncomputable section
namespace ContactIntegerRadicands318
open RationalContactPoint318 ContactRadical318
set_option maxHeartbeats 600000
attribute [-instance] DivisionRing.toRatAlgebra
@[expose] def coefficient : Fin 4 → ℤ := ![-448, -192, 1344, -21]
@[expose] def formIndex : Fin 4 → Fin 5 := ![1,2,3,4]
@[expose] def radicand (u v : ℤ) (i : Fin 4) : ℤ :=
  coefficient i * v * forms u v (formIndex i)
lemma coefficient_ne_zero (i : Fin 4) : coefficient i ≠ 0 := by
  fin_cases i <;> norm_num [coefficient]
lemma v_ne_zero (u v : ℤ) (hn : ∀ j, forms u v j ≠ 0) : v ≠ 0 := hn 0
lemma radicand_ne_zero (u v : ℤ) (hn : ∀ j, forms u v j ≠ 0) (i : Fin 4) :
    radicand u v i ≠ 0 :=
  mul_ne_zero (mul_ne_zero (coefficient_ne_zero i) (v_ne_zero u v hn)) (hn _)

/-- These are the literal integer squares of v times the previously constructed
roots of the independently specified source twist. -/
theorem scaled_parameter (u v : ℤ) (hn : ∀ j, forms u v j ≠ 0) (i : Fin 4) :
    (v : ℚ)^2 * parameters SourceTwistArithmetic318.units
      (32 * ((u : ℚ)/(v : ℚ))) i = (radicand u v i : ℚ) := by
  have hv : (v : ℚ) ≠ 0 := by exact_mod_cast v_ne_zero u v hn
  rw [parameters_eq]
  fin_cases i <;>
    norm_num [SourceTwistArithmetic318.units_val, SourceTwistArithmetic318.constants,
      LinearContactSquareclass318.contacts, radicand, coefficient, formIndex, forms] <;>
    field_simp <;> ring

/-- Exclusion from the actual odd-contact support gives even valuation of
every literal form, including the denominator/infinity form. -/
theorem form_valuation_even (u v : ℤ) (hn : ∀ j, forms u v j ≠ 0)
    (p : ℕ) [Fact p.Prime] (hg : p ∉ badPrimes) (ho : p ∉ contactPrimes u v)
    (j : Fin 5) : Even (padicValInt p (forms u v j)) := by
  by_contra h
  have hod : Odd (padicValInt p (forms u v j)) := Nat.not_even_iff_odd.mp h
  have hd : (p : ℤ) ∣ forms u v j := by
    by_contra hd
    rw [padicValInt.eq_zero_of_not_dvd hd] at hod
    norm_num at hod
  apply ho
  apply (mem_contactPrimes u v p).mpr
  exact ⟨j, Nat.mem_primeFactors.mpr ⟨Fact.out, Int.natCast_dvd.mp hd,
    Int.natAbs_ne_zero.mpr (hn j)⟩, hg, hod⟩

lemma coefficient_valuation_zero (p : ℕ) [Fact p.Prime] (hg : p ∉ badPrimes)
    (i : Fin 4) : padicValInt p (coefficient i) = 0 := by
  have hp : p.Prime := Fact.out
  have h2 := ContactPrimeLimits318.good_not_dvd p 2 hp hg (by simp [badPrimes])
  have h3 := ContactPrimeLimits318.good_not_dvd p 3 hp hg (by simp [badPrimes])
  have h7 := ContactPrimeLimits318.good_not_dvd p 7 hp hg (by simp [badPrimes])
  have h42 : ¬p ∣ 42 := by
    simp only [show 42 = 2*3*7 by norm_num, hp.dvd_mul, h2, h3, h7,
      or_self, not_false_eq_true]
  apply padicValInt.eq_zero_of_not_dvd
  intro h
  have hd : p ∣ (coefficient i).natAbs := Int.natCast_dvd.mp h
  have hk : (coefficient i).natAbs ∣ 42^6 := by fin_cases i <;> norm_num [coefficient]
  exact h42 (hp.dvd_of_dvd_pow (dvd_trans hd hk))

/-- Every literal radicand has even valuation at every good prime outside
the actual odd-contact radical. No replacement by the full radical is made. -/
theorem radicand_valuation_even (u v : ℤ) (hn : ∀ j, forms u v j ≠ 0)
    (p : ℕ) [Fact p.Prime] (hg : p ∉ badPrimes) (ho : p ∉ contactPrimes u v)
    (i : Fin 4) : Even (padicValInt p (radicand u v i)) := by
  rw [radicand, padicValInt.mul
      (mul_ne_zero (coefficient_ne_zero i) (v_ne_zero u v hn)) (hn _),
    padicValInt.mul (coefficient_ne_zero i) (v_ne_zero u v hn),
    coefficient_valuation_zero p hg, zero_add]
  exact (form_valuation_even u v hn p hg ho 0).add
    (form_valuation_even u v hn p hg ho (formIndex i))

end ContactIntegerRadicands318
