module
public import SchemeIsoPushforwardRecovery318
public import OriginalOpenLineRestrictionUnit318
public import Mathlib.CategoryTheory.Functor.FullyFaithful
public section
noncomputable section
namespace SchemeIsoPullbackFullyFaithful318
open AlgebraicGeometry CategoryTheory
universe u
variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso f]
/-- The actual pullback adjunction unit is invertible on a genuine scheme
isomorphism, using its original restriction unit and native comparison. -/
instance unit_app (M : Y.Modules) : IsIso ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M) := by
  rw [←OriginalOpenLineRestrictionUnit318.restriction_unit f M]
  letI := SchemeIsoPushforwardRecovery318.restrictionUnit_isIso f M
  infer_instance
instance unit : IsIso (Scheme.Modules.pullbackPushforwardAdjunction f).unit :=
  NatIso.isIso_of_isIso_app _
@[expose] def fullyFaithful : (Scheme.Modules.pullback f).FullyFaithful :=
  (Scheme.Modules.pullbackPushforwardAdjunction f).fullyFaithfulLOfIsIsoUnit
end SchemeIsoPullbackFullyFaithful318
