module
public import LenstraDVR318
public import Mathlib.NumberTheory.Padics.PadicVal.Basic
public import Mathlib.RingTheory.Coprime.Lemmas
public section
noncomputable section
namespace DVRIntegerValue318
open IsDiscreteValuationRing

/-- At a local ring where p is a nonunit, every integer coprime to p is a unit. -/
theorem isUnit_nat_of_coprime (B:Type*) [CommRing B] [IsLocalRing B]
    (p q:ℕ) (hp:¬IsUnit (p:B)) (hq:Nat.Coprime p q) : IsUnit (q:B) := by
  have hc:IsCoprime (p:B) (q:B) := by
    simpa only [map_natCast] using hq.isCoprime.map (Int.castRingHom B)
  obtain ⟨a,b,hab⟩:=hc
  rcases IsLocalRing.isUnit_or_isUnit_of_add_one hab with h|h
  · exact (hp (isUnit_of_mul_isUnit_right h)).elim
  · exact (isUnit_of_mul_isUnit_right h)

/-- The actual DVR valuation of a nonzero integer is its p-adic order
multiplied by the actual value of p. -/
theorem value_nat (B:Type*) [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    (p n:ℕ) [Fact p.Prime] (hp:¬IsUnit (p:B)) (hn:n≠0) :
    addVal B (n:B)=(padicValNat p n:ℕ∞)*addVal B (p:B) := by
  obtain ⟨q,hq⟩:=pow_padicValNat_dvd (p:=p) (n:=n)
  have hnd:¬p∣q := by
    rintro ⟨k,hk⟩
    apply pow_succ_padicValNat_not_dvd (p:=p) hn
    exact ⟨k,calc
      n = p ^ padicValNat p n * q := hq
      _ = p ^ (padicValNat p n + 1) * k := by rw [hk,pow_succ]; ring⟩
  have hu := isUnit_nat_of_coprime B p q hp ((Fact.out:p.Prime).coprime_iff_not_dvd.mpr hnd)
  nth_rw 1 [hq]
  rw [Nat.cast_mul,Nat.cast_pow,addVal_mul,addVal_eq_zero_iff.mpr hu,
    add_zero,addVal_pow,nsmul_eq_mul]

end DVRIntegerValue318
