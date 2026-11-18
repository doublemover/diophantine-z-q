module
public import OriginalPrimeThreeActualQuotient318
public section
namespace PrimeThreeContactOpen70_318
open OriginalIntegerAffineModel318

/-- Two annihilator witnesses for every ORDERED pair among the four
actual contact constants. Taking a square retains the 3^2 collision
between the last two contacts; dropping that exponent would be invalid. -/
theorem pair_cert (i j : Fin 4) (h : i ≠ j) :
    (contacts i - contacts j) ∣ (3 : ℤ)^2 * 70^10 ∧
    (contacts i - contacts j) ∣ (contacts i - 2)^2 * 70^10 := by
  fin_cases i <;> fin_cases j <;> first | exact (h rfl).elim | decide

private theorem vanishes_if_dvd {k : Type*} [Field k] {a b : ℤ}
    (hab : a ∣ b) (ha : (a : k) = 0) : (b : k) = 0 := by
  obtain ⟨c, rfl⟩ := hab
  rw [Int.cast_mul, ha, zero_mul]

/-- Over any residue field of the explicit arithmetic open D(70),
two different contacts can meet only in characteristic 3 at T=2. -/
theorem collision {k : Type*} [Field k] (h70 : (70 : k) ≠ 0)
    (t : k) (i j : Fin 4) (hij : i ≠ j)
    (hi : t = (contacts i : k)) (hj : t = (contacts j : k)) :
    (3 : k) = 0 ∧ t = 2 := by
  have hd : ((contacts i - contacts j : ℤ) : k) = 0 := by
    rw [Int.cast_sub, sub_eq_zero]
    exact hi.symm.trans hj
  obtain ⟨h1, h2⟩ := pair_cert i j hij
  have hc := vanishes_if_dvd h1 hd
  have ht := vanishes_if_dvd h2 hd
  push_cast at hc ht
  have h3 := (mul_eq_zero.mp hc).resolve_right (pow_ne_zero _ h70)
  have hT := (mul_eq_zero.mp ht).resolve_right (pow_ne_zero _ h70)
  constructor
  · simpa using h3
  · rw [hi]
    apply sub_eq_zero.mp
    simpa using hT

end PrimeThreeContactOpen70_318
