module
public import FifthNormTensorCocycle318
public section
noncomputable section
namespace FifthNormTensorCommon318
open AlgebraicGeometry CategoryTheory
open IntrinsicTensorSheaf318 FifthCompletedGlobal318 FifthChartNorm318
set_option maxHeartbeats 550000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (M N:Model.Modules) {α β:Type} (A:α→Model.Opens) (B:β→Model.Opens)
    (hA:(⊤:Model.Opens)≤⨆i,A i) (hB:(⊤:Model.Opens)≤⨆j,B j)
    (eA:∀i,SheafOfModules.unit (A i).toScheme.ringCatSheaf≅M.restrict (A i).ι)
    (eB:∀j,SheafOfModules.unit (B j).toScheme.ringCatSheaf≅N.restrict (B j).ι)
abbrev leftOpen:=FifthLineTargetCover318.neighborhood M A hA eA
abbrev rightOpen:=FifthLineTargetCover318.neighborhood N B hB eB
@[expose] def common:Target×Target→Target.Opens:=
  UnitCocycleRefinement318.common (leftOpen M A hA eA) (rightOpen N B hB eB)
lemma cover:(⊤:Target.Opens)≤⨆i,common M N A B hA hB eA eB i:=
  UnitCocycleRefinement318.common_cover _ _
    (FifthLineTargetCover318.cover_top M A hA eA) (FifthLineTargetCover318.cover_top N B hB eB)
@[expose] def leftFrame (i:Target×Target):
    SheafOfModules.unit (map⁻¹ᵁcommon M N A B hA hB eA eB i).toScheme.ringCatSheaf≅
      M.restrict (map⁻¹ᵁcommon M N A B hA hB eA eB i).ι:=
  OpenLineFrameRefinement318.frame M (map⁻¹ᵁleftOpen M A hA eA i.1)
    (FifthLineTargetCover318.frame M A hA eA i.1)
    (map⁻¹ᵁcommon M N A B hA hB eA eB i) (map.preimage_mono inf_le_left)
@[expose] def rightFrame (i:Target×Target):
    SheafOfModules.unit (map⁻¹ᵁcommon M N A B hA hB eA eB i).toScheme.ringCatSheaf≅
      N.restrict (map⁻¹ᵁcommon M N A B hA hB eA eB i).ι:=
  OpenLineFrameRefinement318.frame N (map⁻¹ᵁrightOpen N B hB eB i.2)
    (FifthLineTargetCover318.frame N B hB eB i.2)
    (map⁻¹ᵁcommon M N A B hA hB eA eB i) (map.preimage_mono inf_le_right)
/-- The unchanged chosen norm of M, compared with its actual restricted
frames on the whole inverse images of the common target cover. -/
@[expose] def leftIso:FifthNormLineObject318.object M A hA eA≅
    CocycleModule318.object (common M N A B hA hB eA eB) (FifthNormCocycle318.transfer
      (InverseImageLineCocycle318.cocycle map M (common M N A B hA hB eA eB)
        (leftFrame M N A B hA hB eA eB))):=
  FifthNormCoverIso318.iso M (leftOpen M A hA eA) (common M N A B hA hB eA eB)
    (FifthLineTargetCover318.frame M A hA eA) (leftFrame M N A B hA hB eA eB)
    (FifthLineTargetCover318.cover_top M A hA eA) (cover M N A B hA hB eA eB)
@[expose] def rightIso:FifthNormLineObject318.object N B hB eB≅
    CocycleModule318.object (common M N A B hA hB eA eB) (FifthNormCocycle318.transfer
      (InverseImageLineCocycle318.cocycle map N (common M N A B hA hB eA eB)
        (rightFrame M N A B hA hB eA eB))):=
  FifthNormCoverIso318.iso N (rightOpen N B hB eB) (common M N A B hA hB eA eB)
    (FifthLineTargetCover318.frame N B hB eB) (rightFrame M N A B hA hB eA eB)
    (FifthLineTargetCover318.cover_top N B hB eB) (cover M N A B hA hB eA eB)
end FifthNormTensorCommon318
