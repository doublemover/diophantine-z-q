module
public import LenstraVertical318
public section
noncomputable section
namespace LenstraHorizontal318
open Module Algebra IsDiscreteValuationRing Submodule.IsPrincipal
open LenstraVertical318

variable (A K B L:Type*) [CommRing A] [IsDomain A] [Field K]
    [CommRing B] [IsDomain B] [Field L]
    [Algebra A K] [IsFractionRing A K] [Algebra K L] [Algebra A L]
    [Algebra A B] [Algebra B L] [IsScalarTower A K L] [IsScalarTower A B L]
    [FiniteDimensional K L] [CharZero K] [Algebra.IsSeparable K L]
    [IsIntegralClosure B A L] [IsIntegrallyClosed A] [IsDedekindDomain B]
    [IsTorsionFree A B] [IsFractionRing B L] [IsDiscreteValuationRing B]

/-- When the extension degree is a unit, the actual different exponent is
smaller than the value of a nonzero base nonunit. For a base uniformizer this
is the horizontal r≤e−1 bound. -/
theorem different_exponent_lt (x:A) (hx:x≠0) (hu:¬IsUnit x)
    (hn:IsUnit (Module.finrank K L:B)) :
    differentExponent A B < (addVal B (algebraMap A B x)).toNat := by
  have h:=LenstraDVR318.different_value_lt A K B L x hx hu
  rw [addVal_eq_zero_iff.mpr hn,zero_add] at h
  have hxK:algebraMap A K x≠0 :=
    (map_ne_zero_iff (algebraMap A K) (IsFractionRing.injective A K)).mpr hx
  have hxL:algebraMap A L x≠0 := by
    rw [IsScalarTower.algebraMap_apply A K L]
    exact (map_ne_zero_iff (algebraMap K L) (algebraMap K L).injective).mpr hxK
  have hxB:algebraMap A B x≠0 := by
    intro hz
    apply hxL
    rw [IsScalarTower.algebraMap_apply A B L,hz,map_zero]
  have hxf:addVal B (algebraMap A B x)≠⊤ :=
    fun hz=>hxB ((IsDiscreteValuationRing.addVal_eq_top_iff (R:=B)).mp hz)
  have hrf:addVal B (generator (differentIdeal A B))≠⊤ := ne_top_of_lt h
  have hrc:(differentExponent A B:ℕ∞)=addVal B (generator (differentIdeal A B)) :=
    ENat.natCast_toNat hrf
  rw [← hrc,← ENat.natCast_toNat hxf] at h
  exact_mod_cast h

/-- The coefficientwise horizontal domination used in the pullback bound. -/
theorem horizontal_bound (x:A) (hx:x≠0) (hu:¬IsUnit x)
    (hn:IsUnit (Module.finrank K L:B)) :
    differentExponent A B ≤ (addVal B (algebraMap A B x)).toNat-1 := by
  have h:=different_exponent_lt A K B L x hx hu hn
  omega

end LenstraHorizontal318
