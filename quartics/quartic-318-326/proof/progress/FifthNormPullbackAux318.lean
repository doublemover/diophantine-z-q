module
public import LinePullbackCocycleReduction318
public import FifthNormPulledCocycle318
public import FifthNormCoverIso318
public section
noncomputable section
namespace FifthNormPullbackAux318
open AlgebraicGeometry CategoryTheory FifthCompletedGlobal318 FifthChartNorm318
set_option maxHeartbeats 550000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (M:Target.Modules) {ι:Type} (U:ι→Target.Opens)
    (em:∀i,SheafOfModules.unit (U i).toScheme.ringCatSheaf≅M.restrict (U i).ι)
    (hU:(⊤:Target.Opens)≤⨆i,U i)
/-- Explicit pending canonical-frame coherence contract. This auxiliary
consumer does not claim the contract without its independent producer. -/
def Coherent:Prop:=∀(V W:Target.Opens) (h:W≤V)
  (e:SheafOfModules.unit V.toScheme.ringCatSheaf≅M.restrict V.ι),
  OpenLineFrameRefinement318.frame ((Scheme.Modules.pullback map).obj M) (map⁻¹ᵁV)
    (LinePullbackFrames318.frame map M V e) (map⁻¹ᵁW) (map.preimage_mono h)=
  LinePullbackFrames318.frame map M W (OpenLineFrameRefinement318.frame M V e W h)
variable (hc:Coherent M)
include hc in
lemma cocycle_eq:
    InverseImageLineCocycle318.cocycle map ((Scheme.Modules.pullback map).obj M) U
      (fun i=>LinePullbackFrames318.frame map M (U i) (em i))=
    FifthNormCocycle318.pullback (LineFrameCocycle318.cocycle M U em):=
  LinePullbackCocycleReduction318.cocycle map M U em hc
@[expose] def fixedIso:
    CocycleModule318.object U (FifthNormCocycle318.transfer
      (InverseImageLineCocycle318.cocycle map ((Scheme.Modules.pullback map).obj M) U
        (fun i=>LinePullbackFrames318.frame map M (U i) (em i))))≅
    FramedLineTensorPower318.object M 8:=
  CocycleEqualityTransport318.iso U (congrArg FifthNormCocycle318.transfer (cocycle_eq M U em hc))≪≫
    FifthNormPulledCocycle318.iso U M em hU
variable {α:Type} (A:α→Model.Opens) (hA:(⊤:Model.Opens)≤⨆i,A i)
    (eA:∀i,SheafOfModules.unit (A i).toScheme.ringCatSheaf≅
      ((Scheme.Modules.pullback map).obj M).restrict (A i).ι)
/-- Even the auxiliary comparison retains an arbitrary independently
supplied original source presentation, via the genuine cover comparison. -/
@[expose] def chosenIso:
    FifthNormLineObject318.object ((Scheme.Modules.pullback map).obj M) A hA eA≅
    FramedLineTensorPower318.object M 8:=
  FifthNormCoverIso318.iso ((Scheme.Modules.pullback map).obj M)
    (FifthLineTargetCover318.neighborhood ((Scheme.Modules.pullback map).obj M) A hA eA) U
    (FifthLineTargetCover318.frame ((Scheme.Modules.pullback map).obj M) A hA eA)
    (fun i=>LinePullbackFrames318.frame map M (U i) (em i))
    (FifthLineTargetCover318.cover_top ((Scheme.Modules.pullback map).obj M) A hA eA) hU≪≫
    fixedIso M U em hU hc
lemma hom_inv:(chosenIso M U em hU hc A hA eA).hom≫(chosenIso M U em hU hc A hA eA).inv=𝟙 _:=
  (chosenIso M U em hU hc A hA eA).hom_inv_id
lemma inv_hom:(chosenIso M U em hU hc A hA eA).inv≫(chosenIso M U em hU hc A hA eA).hom=𝟙 _:=
  (chosenIso M U em hU hc A hA eA).inv_hom_id
end FifthNormPullbackAux318
