module
public import PrimeThreeCoefficientLocalization318
public import Mathlib.RingTheory.Localization.Basic
public import Mathlib.RingTheory.Localization.Ideal
public import Lean.Elab.Tactic.Omega
public section
noncomputable section
namespace PrimeThreeLocalizationQuotient318

variable (A : Type*) [CommRing A]
abbrev denominators : Submonoid A := Algebra.algebraMapSubmonoid A
  PrimeThreeCoefficientLocalization318.primeIdeal.primeCompl
abbrev threeIdeal : Ideal A := Ideal.span {(3 : A)}
abbrev Fiber := A ⧸ threeIdeal A

/-- Every allowed integer denominator is already a unit modulo three.
The argument applies to every commutative ring, including nonreduced ones. -/
theorem integer_unit (n : ℤ)
    (hn : n ∈ PrimeThreeCoefficientLocalization318.primeIdeal.primeCompl) :
    IsUnit (Ideal.Quotient.mk (threeIdeal A) (n : A)) := by
  have hn' : ¬(3 : ℤ) ∣ n :=
    (PrimeThreeCoefficientLocalization318.mem_complement n).mp hn
  have hm : n % 3 ≠ 0 := by
    intro h
    exact hn' ⟨n / 3, by omega⟩
  have hc : n = 3 * (n / 3) + 1 ∨ n = 3 * (n / 3 + 1) - 1 := by omega
  have h3 : (3 : Fiber A) = 0 := by
    change Ideal.Quotient.mk (threeIdeal A) (3 : A) = 0
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
  rcases hc with h | h
  · rw [h]
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_ofNat, Int.cast_one,
      map_add, map_mul, map_ofNat, map_one, h3, zero_mul, zero_add] using
      (isUnit_one : IsUnit (1 : Fiber A))
  · rw [h]
    simpa only [Int.cast_sub, Int.cast_add, Int.cast_mul, Int.cast_ofNat, Int.cast_one,
      map_sub, map_add, map_mul, map_ofNat, map_one, h3, zero_mul, zero_sub] using
      (isUnit_one.neg : IsUnit (-1 : Fiber A))

theorem quotient_denominators_units :
    Algebra.algebraMapSubmonoid (Fiber A) (denominators A) ≤
      IsUnit.submonoid (Fiber A) := by
  rintro x ⟨a, ⟨n, hn, rfl⟩, rfl⟩
  change IsUnit (Ideal.Quotient.mk (threeIdeal A) (algebraMap ℤ A n))
  simpa only [map_intCast] using integer_unit A n hn

variable (B : Type*) [CommRing B] [Algebra A B]
variable [IsLocalization (denominators A) B]

theorem threeIdeal_map : (threeIdeal A).map (algebraMap A B) = threeIdeal B := by
  simp only [threeIdeal, Ideal.map_span, Set.image_singleton, map_ofNat]

/-- Inverting exactly the integers prime to three does not change the
whole mod-three fiber. No localization in the geometric parameter occurs. -/
@[expose] def quotientEquiv : Fiber A ≃+* Fiber B :=
  (IsLocalization.atUnits (Fiber A)
    (Algebra.algebraMapSubmonoid (Fiber A) (denominators A))
    (S := B ⧸ (threeIdeal A).map (algebraMap A B))
    (quotient_denominators_units A)).toRingEquiv.trans
      (Ideal.quotEquivOfEq (threeIdeal_map A B))

/-- This equivalence is the canonical map on every representative, rather
than an unspecified abstract isomorphism of residue rings. -/
@[simp] theorem quotientEquiv_mk (a : A) :
    quotientEquiv A B (Ideal.Quotient.mk (threeIdeal A) a) =
      Ideal.Quotient.mk (threeIdeal B) (algebraMap A B a) := rfl

end PrimeThreeLocalizationQuotient318
