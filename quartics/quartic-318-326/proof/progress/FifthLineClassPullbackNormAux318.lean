module
public import FifthNormPullbackAux318
public import LineSheafPullback318
public import LineSheafTensorPower318
public import FifthLineClassNormHom318
public section
noncomputable section
namespace FifthLineClassPullbackNormAux318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open FifthCompletedGlobal318 FifthChartNorm318
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (hc:∀M:Target.Modules,FifthNormPullbackAux318.Coherent M)
/-- Auxiliary exact class consumer, retaining its stated pending canonical
restriction coherence premise until the separate producer supplies it. -/
@[expose] def iso (L:Line Target):
    (FifthLineClassNorm318.line (LineSheafPullback318.line map L)).object≅
    (LineSheafTensorPower318.line L 8).object:=
  FifthNormPullbackAux318.chosenIso L.object L.opens L.frame L.cover (hc L.object)
    (LineSheafPullback318.line map L).opens
    (LineSheafPullback318.line map L).cover
    (LineSheafPullback318.line map L).frame
include hc in
lemma norm_pullback (c:Class Target):
    FifthLineClassNormHom318.norm (LineSheafPullback318.pullback map c)=c^8:=by
  induction c using LineSheafClass318.induction with
  | h L => exact (classOf_eq (iso hc L)).trans (LineSheafTensorPower318.classOf_eighth L)
include hc in
lemma kernel_power (c:Class Target) (h:LineSheafPullback318.pullback map c=1):c^8=1:=by
  rw [←norm_pullback hc c,h,map_one]
end FifthLineClassPullbackNormAux318
