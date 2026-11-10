module
public import PELOriginalHolomorphicFibers318
public import QuaternionicPeriodAutomorphy318
public import Mathlib.Analysis.Analytic.Constructions
public section
noncomputable section
namespace PELJointArithmeticLift318
open QuaternionicRealPeriod318 QuaternionicMobiusPeriods318 QuaternionicUnitPeriodTransport318
open QuaternionicJointPeriodTopology318 PELJointPeriodFamily318 PELJointPeriodDeck318
open PELQuaternionRealRepresentation318 PELPrincipalOrderCoordinates318 PELOriginalUnitBiholomorph318
set_option maxHeartbeats 1200000
variable (u : orderˣ) (hu : (unitMatrix representation order u).det=1)

@[expose] def nextParameter (τ : HalfPlane) : HalfPlane :=
  ⟨parameter u τ,parameter_positive u hu τ τ.property⟩
@[expose] def lift (p : Cover) : Cover :=
  (nextParameter u hu p.1,(unitDenominator representation order u p.1)⁻¹ • p.2)
@[expose] def ambientLift (p : Ambient) : Ambient :=
  (unitParameter representation order u p.1,(unitDenominator representation order u p.1)⁻¹ • p.2)

theorem lift_ambient (p : Cover) : ambient (lift u hu p)=ambientLift u (ambient p) := rfl

include hu in
/-- Joint holomorphy of the arithmetic lift, including the varying base and
all fiber coordinates. Nonvanishing is the actual upper-half-plane result. -/
theorem ambientLift_analytic (p : Ambient) (hp : 0<p.1.im) :
    AnalyticAt ℂ (ambientLift u) p := by
  have ht : AnalyticAt ℂ (fun q : Ambient => q.1) p :=
    (ContinuousLinearMap.fst ℂ ℂ ComplexVectors).analyticAt
  have hz : AnalyticAt ℂ (fun q : Ambient => q.2) p :=
    (ContinuousLinearMap.snd ℂ ℂ ComplexVectors).analyticAt
  have hn : AnalyticAt ℂ (fun q : Ambient =>
      (unitMatrix representation order u 0 0:ℂ)*q.1+
        (unitMatrix representation order u 0 1:ℂ)) p :=
    (analyticAt_const.mul ht).add analyticAt_const
  have hd : AnalyticAt ℂ (fun q : Ambient => unitDenominator representation order u q.1) p :=
    (analyticAt_const.mul ht).add analyticAt_const
  have hne := denominator_nonzero u hu p.1 hp
  exact (hn.div hd hne).prod ((hd.inv hne).smul hz)

/-- The total-space map uses the literal original fiber equivalence and
its established identification with the corresponding joint fiber. -/
@[expose] def totalAction (p : Total) : Total :=
  (nextParameter u hu p.1,
    fiberEquiv (nextParameter u hu p.1)
      (transport u hu p.1 p.1.property ((fiberEquiv p.1).symm p.2)))

theorem projection_square (p : Cover) :
    totalAction u hu (familyProjection p)=familyProjection (lift u hu p) := by
  rw [projection_fiber]
  change (nextParameter u hu p.1,
    fiberEquiv (nextParameter u hu p.1)
      (transport u hu p.1 p.1.property ((fiberEquiv p.1).symm
        (fiberEquiv p.1 (QuotientAddGroup.mk' (PELComplexPeriodSurface318.Periods p.1) p.2)))))=_
  rw [AddEquiv.symm_apply_apply]
  exact (projection_fiber (nextParameter u hu p.1)
    ((unitDenominator representation order u p.1)⁻¹ • p.2)).symm

theorem action_over_base (p : Total) : (totalAction u hu p).1=nextParameter u hu p.1 := rfl
end PELJointArithmeticLift318
