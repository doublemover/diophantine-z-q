module
public import TensorSheafNormalization318
public section
noncomputable section
namespace OriginalTensorRightUnit318
open AlgebraicGeometry CategoryTheory Opposite MonoidalCategory
open scoped TensorProduct
set_option maxHeartbeats 650000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X : Scheme.{u}} (M : X.Modules)
local instance presheafMonoidal : MonoidalCategory X.PresheafOfModules :=
  inferInstanceAs (MonoidalCategory (PresheafOfModulesOfCommRing X.presheaf))

/-- The actual tensor right unit for EVERY original module sheaf, obtained
from its original presheaf right unit and sheafification counit. -/
def iso : IntrinsicTensorSheaf318.tensor M (SheafOfModules.unit X.ringCatSheaf) ≅ M :=
  (PresheafOfModules.sheafification (R:=X.ringCatSheaf) (𝟙 X.ringCatSheaf.obj)).mapIso
    (ρ_ M.val) ≪≫ TensorSheafFunctor318.sheafifyIso M

/-- Exact original scalar-action normalization of the canonical right unit,
on every open and every actual pure section. -/
lemma pure (U : X.Opens) (m : Γ(M,U)) (a : Γ(X,U)) :
    (iso M).hom.app U
      (IntrinsicTensorSheaf318.pure M (SheafOfModules.unit X.ringCatSheaf) U m a) = a • m := by
  let g : IntrinsicTensorSheaf318.presheaf M (SheafOfModules.unit X.ringCatSheaf) ⟶ M.val :=
    (ρ_ M.val).hom
  have h1 := congrArg (fun k => k.app (op U) (m ⊗ₜ[Γ(X,U)] a))
    (TensorSheafNormalization318.unit_map g)
  have h2 := congrArg (fun k => k.app (op U) (a • m))
    (TensorSheafNormalization318.unit_counit M)
  change (TensorSheafFunctor318.sheafifyIso M).hom.val.app (op U)
    (((PresheafOfModules.sheafification (R:=X.ringCatSheaf)
      (𝟙 X.ringCatSheaf.obj)).map g).val.app (op U)
      ((OpenSheafification318.unit (IntrinsicTensorSheaf318.presheaf M
        (SheafOfModules.unit X.ringCatSheaf))).app (op U) (m ⊗ₜ[Γ(X,U)] a))) = _
  change ((PresheafOfModules.sheafification (R:=X.ringCatSheaf)
    (𝟙 X.ringCatSheaf.obj)).map g).val.app (op U)
      ((OpenSheafification318.unit (IntrinsicTensorSheaf318.presheaf M
        (SheafOfModules.unit X.ringCatSheaf))).app (op U) (m ⊗ₜ[Γ(X,U)] a)) =
    (OpenSheafification318.unit M.val).app (op U) (a • m) at h1
  rw [h1]
  exact h2
end OriginalTensorRightUnit318
