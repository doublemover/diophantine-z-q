module
public import FractionFiniteCoefficientLift318
public import Mathlib.RingTheory.Algebraic.Basic
public section
noncomputable section
namespace AlgebraicFractionBaseDenominator318
open scoped nonZeroDivisors
variable (R A K:Type*) [CommRing R] [IsDomain R] [CommRing A] [IsDomain A]
  [Field K] [Algebra R A] [Algebra A K] [Algebra R K] [IsScalarTower R A K]
  [IsFractionRing A K] [Algebra.IsAlgebraic R A]
/-- Every fraction of the ACTUAL algebraic order has an ORIGINAL base
ring denominator, not just a denominator belonging to the larger order.
This follows from a genuine annihilating polynomial of that denominator. -/
theorem exists_base_multiple(z:K):
    ∃d:R,d≠0∧∃a:A,algebraMap R K d*z=algebraMap A K a:=by
  obtain ⟨⟨a,b⟩,hab⟩:=IsLocalization.surj A⁰ z
  have hb:(b:A)≠0:=nonZeroDivisors.coe_ne_zero b
  obtain ⟨c,d,hd,hcd⟩:=Algebra.IsAlgebraic.exists_smul_eq_mul R a hb
  refine ⟨d,hd,c,?_⟩
  have hbK:algebraMap A K (b:A)≠0:=by
    simpa only [map_zero] using (IsFractionRing.injective A K).ne hb
  have hm:=congrArg (algebraMap A K) hcd
  simp only [Algebra.smul_def,map_mul,←IsScalarTower.algebraMap_apply R A K] at hm
  apply mul_left_cancel₀ hbK
  calc
    algebraMap A K (b:A)*(algebraMap R K d*z)=
        algebraMap R K d*(z*algebraMap A K (b:A)):=by ring
    _=algebraMap R K d*algebraMap A K a:=by rw [hab]
    _=algebraMap A K (b:A)*algebraMap A K c:=hm

/-- The chosen primitive fraction (or ANY original field element) is
an actual regular element of a produced BASE principal preimage open.
This does not assert that it generates the entire localized order. -/
theorem exists_base_lift (hr:Function.Injective (algebraMap R A))(z:K):
    ∃d:R,∃hd:d≠0,∃ha:algebraMap R A d≠0,
      ∃a:Localization.Away (algebraMap R A d),
        FractionFiniteCoefficientLift318.toField A K (algebraMap R A d) ha a=z:=by
  obtain ⟨d,hd,c,hc⟩:=exists_base_multiple R A K z
  have ha:algebraMap R A d≠0:=by simpa only [map_zero] using hr.ne hd
  let y:Submonoid.powers (algebraMap R A d):=⟨_,⟨1,pow_one _⟩⟩
  refine ⟨d,hd,ha,IsLocalization.mk' (Localization.Away (algebraMap R A d)) c y,?_⟩
  apply (IsLocalization.lift_mk'_spec
    (FractionFiniteCoefficientLift318.powers_units A K (algebraMap R A d) ha) _ _ _).mpr
  simpa only [y,←IsScalarTower.algebraMap_apply R A K] using hc.symm
end AlgebraicFractionBaseDenominator318
