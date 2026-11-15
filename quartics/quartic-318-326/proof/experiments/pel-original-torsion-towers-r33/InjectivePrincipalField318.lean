module
public import Mathlib.RingTheory.Localization.Away.Basic
public section
noncomputable section
namespace InjectivePrincipalField318
variable {R K : Type*} [CommRing R] [Field K]
variable (f : R →+* K) (hf : Function.Injective f) (d : R) (hd : f d ≠ 0)

lemma powers_units (y : Submonoid.powers d) : IsUnit (f y) := by
  obtain ⟨y,⟨n,rfl⟩⟩ := y
  rw [map_pow]
  exact (isUnit_iff_ne_zero.mpr hd).pow n

@[expose] def toField : Localization.Away d →+* K :=
  IsLocalization.lift (powers_units f d hd)

lemma coefficient (a : R) : toField f d hd (algebraMap R (Localization.Away d) a)=f a :=
  IsLocalization.lift_eq _ a

lemma injective : Function.Injective (toField f d hd) := by
  apply (IsLocalization.lift_injective_iff (powers_units f d hd)).mpr
  intro a b
  constructor
  · intro h
    apply hf
    simpa only [coefficient] using congrArg (toField f d hd) h
  · intro h
    rw [hf h]

lemma inverse : toField f d hd ((IsLocalization.Away.invSelf d : Localization.Away d))=(f d)⁻¹ := by
  have h := congrArg (toField f d hd) (IsLocalization.Away.mul_invSelf d (S := Localization.Away d))
  rw [map_mul,coefficient,map_one] at h
  apply mul_left_cancel₀ hd
  rw [h,mul_inv_cancel₀ hd]
end InjectivePrincipalField318
