module
public import LenstraHorizontal318
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public section
noncomputable section
namespace ResidueDifferent318
open Module Algebra IsDiscreteValuationRing IsLocalRing

/-- Positive integers are actual units in a local ring with characteristic-zero residue field. -/
theorem nat_isUnit_of_residue_charZero (B : Type*) [CommRing B] [IsLocalRing B]
    [CharZero (ResidueField B)] (n : ℕ) (hn : n ≠ 0) : IsUnit (n : B) := by
  apply (residue_ne_zero_iff_isUnit (n : B)).mp
  rw [map_natCast]
  exact Nat.cast_ne_zero.mpr hn

variable (A K B L:Type*) [CommRing A] [IsDomain A] [Field K]
    [CommRing B] [IsDomain B] [Field L]
    [Algebra A K] [IsFractionRing A K] [Algebra K L] [Algebra A L]
    [Algebra A B] [Algebra B L] [IsScalarTower A K L] [IsScalarTower A B L]
    [FiniteDimensional K L] [CharZero K] [Algebra.IsSeparable K L]
    [IsIntegralClosure B A L] [IsIntegrallyClosed A] [IsDedekindDomain B]
    [IsTorsionFree A B] [IsFractionRing B L] [IsDiscreteValuationRing B]
    [CharZero (ResidueField B)]

include K L

/-- The source horizontal different bound from actual residue characteristic zero.
No extension-degree unit certificate is supplied. -/
theorem horizontal_bound (x:A) (hx:x≠0) (hu:¬IsUnit x) :
    LenstraVertical318.differentExponent A B ≤
      (addVal B (algebraMap A B x)).toNat - 1 :=
  LenstraHorizontal318.horizontal_bound A K B L x hx hu
    (nat_isUnit_of_residue_charZero B (Module.finrank K L)
      (Module.finrank_pos (R := K) (M := L)).ne')

/-- With the actual ramification index identified, the horizontal coefficient
is at most e-1 without an extra degree-unit or coefficient inequality premise. -/
theorem horizontal_ramification_bound (x:A) (hx:x≠0) (hu:¬IsUnit x)
    (e : ℕ) (he : (addVal B (algebraMap A B x)).toNat = e) :
    LenstraVertical318.differentExponent A B ≤ e - 1 := by
  simpa only [he] using horizontal_bound A K B L x hx hu

end ResidueDifferent318
