module
public import ActualCasselsTateNativeContinuousUnitComparison318
public import ActualCasselsTateTorsionLocalization318
import all ActualCasselsTateContinuousThirdObstruction318
import all ActualCasselsTateContinuousTorsionHThree318
import all ActualCasselsTateTorsionHThreeRestriction318
public section
noncomputable section
namespace ActualCasselsTateNativeCyclotomicDetection318
open ActualCasselsTateContinuousThirdObstruction318 ActualCasselsTateContinuousTorsionHThree318
open ActualCasselsTateTorsionHThreeRestriction318 ActualCasselsTateTorsionLocalization318
open ActualCasselsTateNativeContinuousUnitComparison318
local instance : DecidableEq ℚ := Classical.decEq _
local instance : DecidableEq ℝ := Classical.decEq _

/-- Precisely the finite-module real-place injectivity needed from
arithmetic duality. The actual cochains use roots of unity with their
cyclotomic action; unrestricted unit-valued primitives do not suffice. -/
def RealDetectsCyclotomicThree : Prop :=
  ∀ m : ℕ, 0 < m → Function.Injective (torsionHThreeRestriction m (algebraMap ℚ ℝ))

theorem explicit_class_eq_one (hd : RealDetectsCyclotomicThree)
    (z : continuousUnitThreeCocycles (F:=ℚ)) :
    (QuotientGroup.mk z : ContinuousUnitHThree (F:=ℚ)) = 1 := by
  obtain ⟨m,hm,x,hx,hz⟩ := every_unit_class_lifts_from_real_kernel z
  have h1 : x=1 := hd m hm (hx.trans (map_one _).symm)
  rw [←hz,h1,map_one]

/-- All representative classes supplied from actual continuous 3-cocycles,
on the very same representative, with no Sha condition. -/
theorem native_class_eq_zero (hd : RealDetectsCyclotomicThree)
    (z : continuousUnitThreeCocycles (F:=ℚ)) : nativeUnitThreeClass z = 0 :=
  (nativeUnitThreeClass_eq_zero_iff z).mpr (explicit_class_eq_one hd z)

theorem global_primitive (hd : RealDetectsCyclotomicThree)
    (z : continuousUnitThreeCocycles (F:=ℚ)) :
    ∃ b : continuousUnitTwo (F:=ℚ), continuousUnitDTwo b = z := by
  exact (QuotientGroup.eq_one_iff z).mp (explicit_class_eq_one hd z)
end ActualCasselsTateNativeCyclotomicDetection318
