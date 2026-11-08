module
public import IntrinsicGlobalFrame318
public import Mathlib.AlgebraicGeometry.Properties
public section
noncomputable section
namespace UnitFrameSectionDetection318
open AlgebraicGeometry CategoryTheory Opposite
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
universe u
variable {X:Scheme.{u}} {M:X.Modules}
  (e:M≅SheafOfModules.unit X.ringCatSheaf)

theorem app_injective (U:X.Opens):Function.Injective (e.hom.val.app (op U)):=
  (ConcreteCategory.bijective_of_isIso (e.hom.app U)).1

include e

/-- An actual trivialized module sheaf on an integral scheme has injective
restriction to every nonempty open. The actual frame is an explicit premise. -/
theorem restrict_injective [IsIntegral X] (U V:X.Opens) (h:U≤V) [Nonempty U]:
    Function.Injective (M.presheaf.map (homOfLE h).op):=by
  intro a b hab
  apply app_injective e V
  apply map_injective_of_isIntegral X (homOfLE h)
  have ha:=PresheafOfModules.naturality_apply e.hom.val (homOfLE h).op a
  have hb:=PresheafOfModules.naturality_apply e.hom.val (homOfLE h).op b
  exact ha.symm.trans ((congrArg (e.hom.val.app (op U)) hab).trans hb)

/-- Cancellation in an actual free rank-one sheaf on a nonempty integral open. -/
theorem cancel_scalar [IsIntegral X] (U:X.Opens) [Nonempty U]
    (r:Γ(X,U)) (hr:r≠0) (a b:Γ(M,U)) (h:r • a=r • b):a=b:=by
  apply app_injective e U
  have he:=congrArg (e.hom.val.app (op U)) h
  simp only [map_smul] at he
  change r*(show Γ(X,U) from e.hom.val.app (op U) a)=
    r*(show Γ(X,U) from e.hom.val.app (op U) b) at he
  have hf:(show Γ(X,U) from e.hom.val.app (op U) a)=
      (show Γ(X,U) from e.hom.val.app (op U) b):=mul_left_cancel₀ hr he
  exact hf
end UnitFrameSectionDetection318
