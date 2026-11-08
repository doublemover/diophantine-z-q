module
public import FifthNormCocycle318
public import FramedLineTensorPower318
public import CocycleEqualityTransport318
public section
noncomputable section
namespace FifthNormPulledCocycle318
open AlgebraicGeometry CategoryTheory FifthCompletedGlobal318
set_option maxHeartbeats 350000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {ι:Type} (U:ι→Target.Opens)
/-- The actual whole-overlap unit norm sends pulled original transition
units to their literal eighth powers. This does not yet assert that they
are the extracted frames of the actual module-sheaf pullback. -/
lemma transfer_eq (c:FifthNormCocycle318.TargetCocycle U):
    FifthNormCocycle318.transfer (FifthNormCocycle318.pullback c)=
      UnitCocyclePower318.power c 8:=by
  apply UnitTransitionCocycle318.Cocycle.ext
  intro i j
  exact FifthNormCocycle318.pullback_transition c i j
/-- Actual target eighth tensor power compared with the normed pulled
transition module. Binding to the original source pullback module is a
separate exact frame/transition theorem. -/
@[expose] def iso (M:Target.Modules)
    (em:∀i,SheafOfModules.unit (U i).toScheme.ringCatSheaf≅M.restrict (U i).ι)
    (hc:(⊤:Target.Opens)≤⨆i,U i):
    CocycleModule318.object U (FifthNormCocycle318.transfer
      (FifthNormCocycle318.pullback (LineFrameCocycle318.cocycle M U em)))≅
    FramedLineTensorPower318.object M 8:=
  CocycleEqualityTransport318.iso U (transfer_eq U _)≪≫
    (FramedLineTensorPower318.eighthIso M U em hc).symm
lemma hom_inv (M:Target.Modules)
    (em:∀i,SheafOfModules.unit (U i).toScheme.ringCatSheaf≅M.restrict (U i).ι)
    (hc:(⊤:Target.Opens)≤⨆i,U i):
    (iso U M em hc).hom≫(iso U M em hc).inv=𝟙 _ :=(iso U M em hc).hom_inv_id
lemma inv_hom (M:Target.Modules)
    (em:∀i,SheafOfModules.unit (U i).toScheme.ringCatSheaf≅M.restrict (U i).ι)
    (hc:(⊤:Target.Opens)≤⨆i,U i):
    (iso U M em hc).inv≫(iso U M em hc).hom=𝟙 _ :=(iso U M em hc).inv_hom_id
end FifthNormPulledCocycle318
