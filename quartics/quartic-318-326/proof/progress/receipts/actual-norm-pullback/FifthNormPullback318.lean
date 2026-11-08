module
public import LinePullbackFrameCoherence318
public import FifthLineClassPullbackNormAux318
import all FifthNormPullbackAux318
public section
noncomputable section
namespace FifthNormPullback318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open FifthCompletedGlobal318 FifthChartNorm318
set_option maxHeartbeats 450000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
/-- The exact canonical restriction identity is discharged by its actual
original-map producer, with no remaining coherence premise. -/
lemma coherent (M:Target.Modules):FifthNormPullbackAux318.Coherent M:=by
  unfold FifthNormPullbackAux318.Coherent
  intro V W h e
  exact LinePullbackFrameCoherence318.frame map M V W h e
variable (M:Target.Modules) {ι:Type} (U:ι→Target.Opens)
    (em:∀i,SheafOfModules.unit (U i).toScheme.ringCatSheaf≅M.restrict (U i).ι)
    (hU:(⊤:Target.Opens)≤⨆i,U i)
@[expose] def fixedIso:=FifthNormPullbackAux318.fixedIso M U em hU (coherent M)
variable {α:Type} (A:α→Model.Opens) (hA:(⊤:Model.Opens)≤⨆i,A i)
    (eA:∀i,SheafOfModules.unit (A i).toScheme.ringCatSheaf≅
      ((Scheme.Modules.pullback map).obj M).restrict (A i).ι)
@[expose] def iso:
    FifthNormLineObject318.object ((Scheme.Modules.pullback map).obj M) A hA eA≅
    FramedLineTensorPower318.object M 8:=
  FifthNormPullbackAux318.chosenIso M U em hU (coherent M) A hA eA
lemma hom_inv:(iso M U em hU A hA eA).hom≫(iso M U em hU A hA eA).inv=𝟙 _:=
  (iso M U em hU A hA eA).hom_inv_id
lemma inv_hom:(iso M U em hU A hA eA).inv≫(iso M U em hU A hA eA).hom=𝟙 _:=
  (iso M U em hU A hA eA).inv_hom_id
@[expose] def lineIso (L:Line Target):
    (FifthLineClassNorm318.line (LineSheafPullback318.line map L)).object≅
    (LineSheafTensorPower318.line L 8).object:=
  FifthLineClassPullbackNormAux318.iso coherent L
lemma norm_pullback (c:Class Target):
    FifthLineClassNormHom318.norm (LineSheafPullback318.pullback map c)=c^8:=
  FifthLineClassPullbackNormAux318.norm_pullback coherent c
lemma kernel_power (c:Class Target) (h:LineSheafPullback318.pullback map c=1):c^8=1:=
  FifthLineClassPullbackNormAux318.kernel_power coherent c h
end FifthNormPullback318
