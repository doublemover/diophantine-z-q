module
public import Mathlib.NumberTheory.Padics.PadicVal.Basic
public import Mathlib.RingTheory.Coprime.Lemmas
public import Mathlib.RingTheory.DedekindDomain.Different
public import Mathlib.RingTheory.Valuation.ValuationRing
public import Mathlib.Tactic

public section
noncomputable section
namespace SelectedJOneDirectLenstraClear318

open scoped nonZeroDivisors

abbrev exponent (M : ℕ) : ℕ := Nat.log 2 (M ^ 2) + 1
abbrev multiplier (M : ℕ) : ℕ := M ^ exponent M

theorem padic_lt_exponent {p M d : ℕ} [Fact p.Prime]
    (hd : 0 < d) (hdegree : d ≤ M ^ 2) :
    padicValNat p d < exponent M := by
  have hp : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hpown : p ^ padicValNat p d ≤ d :=
    Nat.le_of_dvd hd (pow_padicValNat_dvd (p := p) (n := d))
  have htwo : 2 ^ padicValNat p d ≤ p ^ padicValNat p d :=
    Nat.pow_le_pow_left hp _
  exact Nat.lt_succ_of_le (Nat.le_log_of_pow_le (by decide : 1 < 2)
    (htwo.trans (hpown.trans hdegree)))

/-- Cancellation in the base domain and Bézout detect a p-denominator
without assigning the absolute p-valuation any particular value. -/
theorem natCast_pow_not_dvd (A : Type*) [CommRing A] [IsDomain A] [CharZero A]
    {p d k : ℕ} [Fact p.Prime] (hp : ¬IsUnit (p : A))
    (hd : d ≠ 0) (hj : padicValNat p d < k) :
    ¬ (p : A) ^ k ∣ (d : A) := by
  intro hdiv
  obtain ⟨c, hc⟩ := pow_padicValNat_dvd (p := p) (n := d)
  have hnpc : ¬ p ∣ c := by
    rintro ⟨r, hr⟩
    apply pow_succ_padicValNat_not_dvd (p := p) hd
    refine ⟨r, ?_⟩
    calc
      d = p ^ padicValNat p d * c := hc
      _ = p ^ (padicValNat p d + 1) * r := by rw [hr, pow_succ]; ring
  obtain ⟨x, hx⟩ :
      (p : A) ^ (padicValNat p d + 1) ∣ (d : A) :=
    (pow_dvd_pow (p : A) (Nat.succ_le_of_lt hj)).trans hdiv
  have hcn : (d : A) = (p : A) ^ padicValNat p d * (c : A) := by
    simpa only [Nat.cast_mul, Nat.cast_pow] using congrArg (fun n : ℕ => (n : A)) hc
  have hp0 : (p : A) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  have hcA : (c : A) = (p : A) * x := by
    apply mul_left_cancel₀ (pow_ne_zero (padicValNat p d) hp0)
    calc
      _ = (d : A) := hcn.symm
      _ = (p : A) ^ (padicValNat p d + 1) * x := hx
      _ = _ := by rw [pow_succ, mul_assoc]
  have hcop : IsCoprime (p : A) (c : A) := by
    have hnat : Nat.Coprime p c := (Fact.out : p.Prime).coprime_iff_not_dvd.mpr hnpc
    simpa only [map_natCast] using hnat.isCoprime.map (Int.castRingHom A)
  obtain ⟨a, b, hab⟩ := hcop
  apply hp
  refine isUnit_iff_exists_inv.mpr ⟨a + b * x, ?_⟩
  calc
    _ = a * (p : A) + b * ((p : A) * x) := by ring
    _ = 1 := by rw [← hcA, hab]

/-- The trace value d/N has a p-denominator in the actual fraction field.
The hypotheses are on the level and extension degree, not on the different. -/
theorem cast_degree_div_not_mem_base (A K : Type*) [CommRing A] [IsDomain A]
    [CharZero A] [Field K] [CharZero K] [Algebra A K] [IsFractionRing A K]
    {p M d : ℕ} [Fact p.Prime] (hp : ¬IsUnit (p : A))
    (hM : M ≠ 0) (hpM : p ∣ M) (hd : 0 < d) (hdegree : d ≤ M ^ 2) :
    (d : K) / (multiplier M : K) ∉ (algebraMap A K).range := by
  rintro ⟨x, hx⟩
  have hN : (multiplier M : K) ≠ 0 := Nat.cast_ne_zero.mpr (pow_ne_zero _ hM)
  have hmul : algebraMap A K ((multiplier M : A) * x) =
      algebraMap A K (d : A) := by
    simp only [map_mul, map_natCast, hx]
    exact (mul_comm _ _).trans (div_mul_cancel₀ _ hN)
  have hdvd : (multiplier M : A) ∣ (d : A) :=
    ⟨x, (IsFractionRing.injective A K hmul).symm⟩
  obtain ⟨c, hc⟩ := pow_dvd_pow_of_dvd hpM (exponent M)
  have hpow : (p : A) ^ exponent M ∣ (multiplier M : A) := by
    refine ⟨(c : A), ?_⟩
    simpa only [Nat.cast_mul, Nat.cast_pow] using congrArg (fun n : ℕ => (n : A)) hc
  exact natCast_pow_not_dvd A hp hd.ne' (padic_lt_exponent hd hdegree) (hpow.trans hdvd)

section SignedFactor

variable (A K B L : Type*) [CommRing A] [IsDomain A] [CharZero A]
    [Field K] [CharZero K] [CommRing B] [IsDedekindDomain B] [PreValuationRing B] [Field L]
    [Algebra A K] [IsFractionRing A K] [Algebra K L] [Algebra A L]
    [Algebra A B] [Algebra B L] [IsScalarTower A K L] [IsScalarTower A B L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] [IsIntegralClosure B A L]
    [IsIntegrallyClosed A] [IsTorsionFree A B] [IsFractionRing B L]

/-- Use the reciprocal of the exact level multiplier directly in the
trace-dual test. The strict inclusion is the required bad-prime different
bound on the signed factor, without expressing it in uniformizer coordinates. -/
theorem local_span_lt_different (p M : ℕ) [Fact p.Prime] (hp : ¬IsUnit (p : B))
    (hM : M ≠ 0) (hpM : p ∣ M) (hdegree : Module.finrank K L ≤ M ^ 2) :
    Ideal.span {(multiplier M : B)} < differentIdeal A B := by
  let b : B := multiplier M
  let y : L := algebraMap K L ((multiplier M : K)⁻¹)
  have hN : (multiplier M : K) ≠ 0 := Nat.cast_ne_zero.mpr (pow_ne_zero _ hM)
  have hmap : algebraMap B L b = algebraMap K L (multiplier M : K) := by
    simp only [b, map_natCast]
  have hb : b ≠ 0 := by
    intro h
    have hz : algebraMap K L (multiplier M : K) = 0 := by
      rw [← hmap, h, map_zero]
    exact hN ((algebraMap K L).injective (by simpa only [map_zero] using hz))
  have hy : y = (algebraMap B L b)⁻¹ := by
    change algebraMap K L ((multiplier M : K)⁻¹) = (algebraMap B L b)⁻¹
    rw [hmap, map_inv₀]
  have hymem : y ∈ ((Ideal.span {b} : Ideal B)⁻¹ : FractionalIdeal B⁰ L) := by
    rw [FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.spanSingleton_inv, hy]
    exact FractionalIdeal.mem_spanSingleton_self _ _
  have ht : Algebra.trace K L y = (Module.finrank K L : K) / (multiplier M : K) := by
    dsimp only [y]
    rw [Algebra.trace_algebraMap, nsmul_eq_mul, div_eq_mul_inv]
  have hpA : ¬IsUnit (p : A) := fun h =>
    hp (by simpa only [map_natCast] using h.map (algebraMap A B))
  have hnot : ¬ differentIdeal A B ≤ Ideal.span {b} := by
    intro hle
    have htr := (differentialIdeal_le_iff (A := A) (K := K) (L := L)
      (I := Ideal.span {b}) (Ideal.span_singleton_eq_bot.not.mpr hb)).mp hle
    have hmem : Algebra.trace K L y ∈ (1 : Submodule A K) :=
      htr (Submodule.mem_map.mpr ⟨y, hymem, rfl⟩)
    rw [ht] at hmem
    exact cast_degree_div_not_mem_base A K hpA hM hpM Module.finrank_pos hdegree
      (Submodule.mem_one.mp hmem)
  have htotal := (PreValuationRing.iff_ideal_total (R := B)).mp
    (inferInstance : PreValuationRing B)
  exact lt_of_le_not_ge ((htotal.total (Ideal.span {b}) (differentIdeal A B)).resolve_right hnot) hnot

theorem local_mem_different (p M : ℕ) [Fact p.Prime] (hp : ¬IsUnit (p : B))
    (hM : M ≠ 0) (hpM : p ∣ M) (hdegree : Module.finrank K L ≤ M ^ 2) :
    (multiplier M : B) ∈ differentIdeal A B :=
  (local_span_lt_different A K B L p M hp hM hpM hdegree).le
    (Ideal.mem_span_singleton_self _)

end SignedFactor
end SelectedJOneDirectLenstraClear318

#print axioms SelectedJOneDirectLenstraClear318.local_span_lt_different
#print axioms SelectedJOneDirectLenstraClear318.local_mem_different
