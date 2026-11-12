module
public import IntrinsicTensorSheaf318
public section
noncomputable section
namespace TensorSheafFunctor318
open AlgebraicGeometry CategoryTheory MonoidalCategory
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
universe u
variable {X : Scheme.{u}}
local instance presheafMonoidal : MonoidalCategory X.PresheafOfModules :=
  inferInstanceAs (MonoidalCategory (PresheafOfModulesOfCommRing X.presheaf))

@[expose] def congr {M M' N N' : X.Modules} (e : M ≅ M') (f : N ≅ N') :
    IntrinsicTensorSheaf318.tensor M N ≅ IntrinsicTensorSheaf318.tensor M' N' :=
  (PresheafOfModules.sheafification (R:=X.ringCatSheaf) (𝟙 X.ringCatSheaf.obj)).mapIso
    (tensorIso ((Scheme.Modules.toPresheafOfModules X).mapIso e)
      ((Scheme.Modules.toPresheafOfModules X).mapIso f))

@[expose] def sheafifyIso (M : X.Modules) :
    (PresheafOfModules.sheafification (R:=X.ringCatSheaf)
      (𝟙 X.ringCatSheaf.obj)).obj M.val ≅ M :=
  asIso ((PresheafOfModules.sheafificationAdjunction (R:=X.ringCatSheaf)
    (𝟙 X.ringCatSheaf.obj)).counit.app M)

/-- New continuation: the genuine tensor square of O is O. -/
@[expose] def unitIso :
    IntrinsicTensorSheaf318.tensor (SheafOfModules.unit X.ringCatSheaf)
      (SheafOfModules.unit X.ringCatSheaf) ≅ SheafOfModules.unit X.ringCatSheaf :=
  (PresheafOfModules.sheafification (R:=X.ringCatSheaf) (𝟙 X.ringCatSheaf.obj)).mapIso
    (λ_ (PresheafOfModulesOfCommRing.unit X.presheaf)) ≪≫
      sheafifyIso (SheafOfModules.unit X.ringCatSheaf)
end TensorSheafFunctor318
