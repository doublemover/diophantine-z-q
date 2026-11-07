module
public import LenstraVertical318
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public section
noncomputable section
namespace DVRRamification318
open Module Algebra IsDiscreteValuationRing IsLocalRing

/-- The residue characteristic is a nonunit in the actual local ring. -/
theorem residue_prime_not_unit (B:Type*) [CommRing B] [IsLocalRing B]
    (p:ℕ) [CharP (ResidueField B) p] : ¬IsUnit (p:B) := by
  intro h
  have hz:residue B (p:B)≠0 := (residue_ne_zero_iff_isUnit (p:B)).mpr h
  apply hz
  rw [map_natCast,CharP.cast_eq_zero]

/-- Restricting the actual DVR valuation through a ring homomorphism scales
by the actual value of a uniformizer. No ramification-value identity is assumed. -/
theorem value_map (A B:Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    (f:A→+*B) (pi:A) (hpi:Irreducible pi) (x:A) (hx:x≠0) :
    addVal B (f x)=(addVal A x).toNat • addVal B (f pi) := by
  obtain ⟨n,u,hu⟩:=eq_unit_mul_pow_irreducible hx hpi
  have hv:addVal A x=n := addVal_def x u hpi n hu
  rw [hv,ENat.toNat_natCast,hu,map_mul,map_pow,addVal_mul,
    addVal_eq_zero_iff.mpr (u.isUnit.map f),zero_add,addVal_pow]

/-- Natural exponents multiply through an injective homomorphism of actual DVRs. -/
theorem value_map_nat (A B:Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    (f:A→+*B) (hf:Function.Injective f) (pi:A) (hpi:Irreducible pi)
    (x:A) (hx:x≠0) :
    (addVal B (f x)).toNat=(addVal B (f pi)).toNat*(addVal A x).toNat := by
  have hp0:f pi≠0 := (map_ne_zero_iff f hf).mpr hpi.ne_zero
  have hpf:addVal B (f pi)≠⊤ := fun h=>hp0 ((addVal_eq_top_iff (R:=B)).mp h)
  rw [value_map A B f pi hpi x hx,nsmul_eq_mul,← ENat.natCast_toNat hpf]
  simp only [← Nat.cast_mul,ENat.toNat_natCast,mul_comm]

end DVRRamification318
