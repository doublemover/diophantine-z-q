module
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Int.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Multiplicity
public import Mathlib.RingTheory.PrincipalIdealDomain
public section
noncomputable section
namespace PrimeThreeCoefficientLocalization318

abbrev primeIdeal : Ideal ℤ := Ideal.span {(3 : ℤ)}
instance primeIdeal_prime : primeIdeal.IsPrime :=
  (Ideal.span_singleton_prime (by norm_num : (3 : ℤ) ≠ 0)).mpr
    (Int.prime_iff_natAbs_prime.mpr (by norm_num))
abbrev Coeff := Localization.AtPrime primeIdeal
abbrev parameter : Coeff := algebraMap ℤ Coeff 3

/-- The exact complement of (3), not the complement of zero. -/
theorem mem_complement (s : ℤ) : s ∈ primeIdeal.primeCompl ↔ ¬(3 : ℤ) ∣ s := by
  change s ∉ Ideal.span {(3 : ℤ)} ↔ _
  rw [Ideal.mem_span_singleton]

theorem integer_map_unit (s : primeIdeal.primeCompl) :
    IsUnit (algebraMap ℤ ℚ s) := by
  apply IsUnit.mk0
  intro hs
  have hz : (s : ℤ) = 0 := (Int.castRingHom ℚ).injective_int (by simpa using hs)
  exact s.property (hz ▸ primeIdeal.zero_mem)

/-- The coefficient localization is embedded in the actual rational numbers. -/
@[expose] def rationalMap : Coeff →+* ℚ :=
  IsLocalization.lift (S := Coeff) integer_map_unit

@[simp] theorem rationalMap_integer (a : ℤ) :
    rationalMap (algebraMap ℤ Coeff a) = algebraMap ℤ ℚ a :=
  IsLocalization.lift_eq integer_map_unit a

@[expose] def rationalAlgebra : Algebra Coeff ℚ := rationalMap.toAlgebra
attribute [local instance] rationalAlgebra

instance integer_rational_tower : @IsScalarTower ℤ Coeff ℚ
    (inferInstance : Algebra ℤ Coeff).toSMul
    rationalAlgebra.toSMul (inferInstance : Algebra ℤ ℚ).toSMul :=
  IsScalarTower.of_algebraMap_eq (R := ℤ) (S := Coeff) (A := ℚ)
    (fun a => (rationalMap_integer a).symm)

theorem rationalMap_injective : Function.Injective rationalMap := by
  apply (IsLocalization.injective_iff_map_algebraMap_eq primeIdeal.primeCompl rationalMap).mpr
  intro a b
  rw [rationalMap_integer, rationalMap_integer]
  exact (IsLocalization.injective Coeff primeIdeal.primeCompl_le_nonZeroDivisors).eq_iff.trans
    (Int.castRingHom ℚ).injective_int.eq_iff.symm

/-- Every nonzero integer has a finite power of three and a denominator
already invertible in Z_(3). No factorization or local-field premise is assumed. -/
theorem denominator_factor (d : ℤ) (hd : d ≠ 0) :
    ∃ n : ℕ, ∃ s : ℤ, d = 3 ^ n * s ∧ s ∈ primeIdeal.primeCompl := by
  have hm : FiniteMultiplicity (3 : ℤ) d := Int.finiteMultiplicity_iff.mpr
    ⟨by norm_num, hd⟩
  obtain ⟨s, hs, h3s⟩ := hm.exists_eq_pow_mul_and_not_dvd
  exact ⟨multiplicity (3 : ℤ) d, s, hs, (mem_complement s).mpr h3s⟩

/-- Inverting only three after localizing integer coefficients at (3)
produces Q, with its literal coefficient embedding. -/
theorem rational_away : IsLocalization.Away parameter ℚ := by
  apply (isLocalization_iff (Submonoid.powers parameter) ℚ).mpr
  have hp : IsUnit (algebraMap Coeff ℚ parameter) := by
    change IsUnit (rationalMap (algebraMap ℤ Coeff 3))
    rw [rationalMap_integer]
    norm_num
  refine ⟨?_, ?_, ?_⟩
  · intro y
    obtain ⟨n, hn⟩ := y.property
    change IsUnit (algebraMap Coeff ℚ y.val)
    rw [← hn, map_pow]
    exact hp.pow n
  · intro z
    obtain ⟨⟨a, d⟩, hz⟩ := IsLocalization.surj (nonZeroDivisors ℤ) z
    obtain ⟨n, s, hds, hs⟩ := denominator_factor d
      (mem_nonZeroDivisors_iff_ne_zero.mp d.property)
    let b : Coeff := IsLocalization.mk' Coeff a ⟨s, hs⟩
    have hb : rationalMap b * algebraMap ℤ ℚ s = algebraMap ℤ ℚ a := by
      have h := congrArg rationalMap (IsLocalization.mk'_spec Coeff a ⟨s, hs⟩)
      simpa only [map_mul, rationalMap_integer] using h
    have hsQ : algebraMap ℤ ℚ s ≠ 0 := (integer_map_unit ⟨s, hs⟩).ne_zero
    have hdQ : algebraMap ℤ ℚ d = (3 : ℚ) ^ n * algebraMap ℤ ℚ s := by
      simpa only [map_mul, map_pow, map_ofNat] using congrArg (algebraMap ℤ ℚ) hds
    refine ⟨⟨b, ⟨parameter ^ n, ⟨n, rfl⟩⟩⟩, ?_⟩
    change z * rationalMap (parameter ^ n) = rationalMap b
    rw [map_pow, rationalMap_integer]
    norm_num only [map_ofNat]
    apply mul_right_cancel₀ hsQ
    rw [mul_assoc, ← hdQ]
    exact hz.trans hb.symm
  · intro x y h
    refine ⟨1, ?_⟩
    simpa only [OneMemClass.coe_one, one_mul] using rationalMap_injective h

end PrimeThreeCoefficientLocalization318
