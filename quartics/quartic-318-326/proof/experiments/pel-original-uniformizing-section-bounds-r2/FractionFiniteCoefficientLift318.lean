module
public import Mathlib.RingTheory.Localization.Integer
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public section
noncomputable section
namespace FractionFiniteCoefficientLift318
open scoped nonZeroDivisors
variable (R K:Type*) [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
variable (d:R)(hd:d≠0)
lemma powers_units(y:Submonoid.powers d):IsUnit (algebraMap R K y):=by
  obtain ⟨y,⟨n,rfl⟩⟩:=y
  rw [map_pow]
  have h:algebraMap R K d≠0:=by
    simpa only [map_zero] using (IsFractionRing.injective R K).ne hd
  exact (isUnit_iff_ne_zero.mpr h).pow n
@[expose] def toField:Localization.Away d→+*K:=
  IsLocalization.lift (powers_units R K d hd)
lemma toField_coefficient(a:R):toField R K d hd (algebraMap R (Localization.Away d) a)=
    algebraMap R K a:=IsLocalization.lift_eq _ a
lemma toField_injective:Function.Injective (toField R K d hd):=by
  apply (IsLocalization.lift_injective_iff (powers_units R K d hd)).mpr
  intro a b
  have hi:Function.Injective (algebraMap R (Localization.Away d)):=
    IsLocalization.injective _ (powers_le_nonZeroDivisors_of_noZeroDivisors hd)
  exact hi.eq_iff.trans (IsFractionRing.injective R K).eq_iff.symm

/-- EVERY finite family in the original fraction field admits one
nonzero ORIGINAL-ring denominator and exact lifts into its literal
principal localization. The map back to the field is injective and
fixes original coefficients, so polynomial identities can descend. -/
theorem exists_lift {ι:Type*} [Finite ι](f:ι→K):
    ∃d:R,∃hd:d≠0,∃g:ι→Localization.Away d,
      ∀i,toField R K d hd (g i)=f i:=by
  obtain ⟨d,hd⟩:=IsLocalization.exist_integer_multiples_of_finite R⁰ f
  choose a ha using hd
  have hd0:(d:R)≠0:=nonZeroDivisors.coe_ne_zero d
  let y:Submonoid.powers (d:R):=⟨d,⟨1,pow_one _⟩⟩
  refine ⟨d,hd0,fun i=>IsLocalization.mk' (Localization.Away (d:R)) (a i) y,?_⟩
  intro i
  apply (IsLocalization.lift_mk'_spec (powers_units R K d hd0) _ _ _).mpr
  simpa only [y,Algebra.smul_def] using ha i
end FractionFiniteCoefficientLift318
