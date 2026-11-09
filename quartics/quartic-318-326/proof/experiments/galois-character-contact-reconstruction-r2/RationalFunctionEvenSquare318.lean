module
public import PolynomialEvenSquare318
public import Mathlib.FieldTheory.RatFunc.Basic
public section
noncomputable section
open scoped BigOperators
namespace RationalFunctionEvenSquare318
open Polynomial
variable {F : Type*} [Field F]

/-- The actual signed order of the canonical coprime numerator and denominator. -/
@[expose] def orderAt (q : F[X]) (x : RatFunc F) : ℤ :=
  (multiplicity q x.num : ℤ) - (multiplicity q x.denom : ℤ)

/-- Coprimality prevents an unobserved even cancellation between numerator
and denominator. Every prime polynomial, of any residue degree, is included. -/
theorem reduced_even (x : RatFunc F)
    (h : ∀ q : F[X], Prime q → Even (orderAt q x)) :
    ∀ q : F[X], Prime q →
      Even (multiplicity q x.num) ∧ Even (multiplicity q x.denom) := by
  intro q hq
  have hh := h q hq
  unfold orderAt at hh
  by_cases hn : q ∣ x.num
  · have hd : ¬ q ∣ x.denom := fun hd =>
      hq.not_isUnit ((RatFunc.isCoprime_num_denom x).isUnit_of_dvd' hn hd)
    have hz := multiplicity_eq_zero_of_not_dvd hd
    rw [hz] at hh ⊢
    norm_num at hh ⊢
    exact_mod_cast hh
  · have hz := multiplicity_eq_zero_of_not_dvd hn
    rw [hz] at hh ⊢
    norm_num at hh ⊢
    exact_mod_cast hh

/-- An everywhere-even finite divisor of a rational function leaves exactly
one base-field scalar squareclass. This is a global identity, valid also at
infinity, not a check limited to the four known finite contacts. -/
theorem scalar_square (x : RatFunc F) (hx : x ≠ 0)
    (h : ∀ q : F[X], Prime q → Even (orderAt q x)) :
    ∃ (c : F) (z : RatFunc F), c ≠ 0 ∧ z ≠ 0 ∧ x = RatFunc.C c * z ^ 2 := by
  have he := reduced_even x h
  obtain ⟨c, r, hc, hr⟩ := PolynomialEvenSquare318.scalar_square x.num
    (RatFunc.num_ne_zero hx) (fun q hq => (he q hq).1)
  obtain ⟨d, s, hd, hs⟩ := PolynomialEvenSquare318.scalar_square x.denom
    (RatFunc.denom_ne_zero x) (fun q hq => (he q hq).2)
  let z : RatFunc F := algebraMap F[X] (RatFunc F) r / algebraMap F[X] (RatFunc F) s
  have hf : x = RatFunc.C (c / d) * z ^ 2 := by
    rw [← RatFunc.num_div_denom x, hr, hs]
    simp only [map_mul, map_pow, RatFunc.algebraMap_C, map_div, z, div_pow]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_pow]
    ring
  have hz : z ≠ 0 := by
    intro hzero
    apply hx
    simpa [hzero] using hf
  exact ⟨c / d, z, div_ne_zero hc hd, hz, hf⟩
end RationalFunctionEvenSquare318
