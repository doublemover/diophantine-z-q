module
public import InverseImageLineCocycle318
public import FifthLineTargetCover318
public import FifthNormCocycle318
public section
noncomputable section
namespace FifthLineExtractedCocycle318
open AlgebraicGeometry CategoryTheory TopologicalSpace
open FifthCompletedGlobal318 FifthChartNorm318
set_option maxHeartbeats 650000
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (M:Model.Modules) {κ:Type} (V:κ→Model.Opens)
    (hc:(⊤:Model.Opens)≤⨆i,V i)
    (frames:∀i,SheafOfModules.unit ((V i):Scheme).ringCatSheaf≅M.restrict (V i).ι)
/-- The actual original line now supplies source transition data on a genuine
target cover, rather than assuming a target-pullback presentation. -/
@[expose] def source:FifthNormCocycle318.SourceCocycle
    (FifthLineTargetCover318.neighborhood M V hc frames):=
  InverseImageLineCocycle318.cocycle map M
    (FifthLineTargetCover318.neighborhood M V hc frames)
    (FifthLineTargetCover318.frame M V hc frames)
/-- The exact regular-unit norm applied to these constructed original line
transitions. A target line object is the separate cocycle-gluing consumer. -/
@[expose] def target:FifthNormCocycle318.TargetCocycle
    (FifthLineTargetCover318.neighborhood M V hc frames):=
  FifthNormCocycle318.transfer (source M V hc frames)
lemma target_transition (i j:Target):
    (target M V hc frames).transition i j=
      FifthOpenNorm318.unitNorm.app (Opposite.op
        (FifthLineTargetCover318.neighborhood M V hc frames i⊓
          FifthLineTargetCover318.neighborhood M V hc frames j))
        ((source M V hc frames).transition i j):=rfl
end FifthLineExtractedCocycle318
