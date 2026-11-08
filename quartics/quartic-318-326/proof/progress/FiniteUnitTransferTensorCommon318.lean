module
public import UnitTransferTensorIso318
public section
noncomputable section
namespace FiniteUnitTransferTensorCommon318
open AlgebraicGeometry CategoryTheory
open IntrinsicTensorSheaf318 UnitTransferGaugeIso318 FiniteUnitTransferPresentation318
set_option maxHeartbeats 550000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X Y:Scheme.{u}} (f:X⟶Y) [IsFinite f]
    (unitMap:StructureUnitsSheaf318.pushedUnits f⟶StructureUnitsSheaf318.units Y)
    (M N:X.Modules) {α β:Type u} (A:α→X.Opens) (B:β→X.Opens)
    (hA:(⊤:X.Opens)≤⨆i,A i) (hB:(⊤:X.Opens)≤⨆j,B j)
    (eA:∀i,SheafOfModules.unit (A i).toScheme.ringCatSheaf≅M.restrict (A i).ι)
    (eB:∀j,SheafOfModules.unit (B j).toScheme.ringCatSheaf≅N.restrict (B j).ι)
abbrev leftOpen:=targetOpen f M A hA eA
abbrev rightOpen:=targetOpen f N B hB eB
@[expose] def common:Y×Y→Y.Opens:=
  UnitCocycleRefinement318.common (leftOpen f M A hA eA) (rightOpen f N B hB eB)
lemma cover:(⊤:Y.Opens)≤⨆i,common f M N A B hA hB eA eB i:=
  UnitCocycleRefinement318.common_cover _ _
    (target_cover f M A hA eA) (target_cover f N B hB eB)
@[expose] def leftFrame (i:Y×Y):
    SheafOfModules.unit (f⁻¹ᵁcommon f M N A B hA hB eA eB i).toScheme.ringCatSheaf≅
      M.restrict (f⁻¹ᵁcommon f M N A B hA hB eA eB i).ι:=
  OpenLineFrameRefinement318.frame M (f⁻¹ᵁleftOpen f M A hA eA i.1)
    (sourceFrame f M A hA eA i.1)
    (f⁻¹ᵁcommon f M N A B hA hB eA eB i) (f.preimage_mono inf_le_left)
@[expose] def rightFrame (i:Y×Y):
    SheafOfModules.unit (f⁻¹ᵁcommon f M N A B hA hB eA eB i).toScheme.ringCatSheaf≅
      N.restrict (f⁻¹ᵁcommon f M N A B hA hB eA eB i).ι:=
  OpenLineFrameRefinement318.frame N (f⁻¹ᵁrightOpen f N B hB eB i.2)
    (sourceFrame f N B hB eB i.2)
    (f⁻¹ᵁcommon f M N A B hA hB eA eB i) (f.preimage_mono inf_le_right)
/-- The unchanged chosen norm of M, compared with its actual restricted
frames on the whole inverse images of the common target cover. -/
@[expose] def leftIso:FiniteUnitTransferLine318.object f M A hA eA unitMap≅
    CocycleModule318.object (common f M N A B hA hB eA eB) (transfer f unitMap (common f M N A B hA hB eA eB)
      (InverseImageLineCocycle318.cocycle f M (common f M N A B hA hB eA eB)
        (leftFrame f M N A B hA hB eA eB))):=
  UnitTransferCoverIso318.iso f unitMap M (leftOpen f M A hA eA) (common f M N A B hA hB eA eB)
    (sourceFrame f M A hA eA) (leftFrame f M N A B hA hB eA eB)
    (target_cover f M A hA eA) (cover f M N A B hA hB eA eB)
@[expose] def rightIso:FiniteUnitTransferLine318.object f N B hB eB unitMap≅
    CocycleModule318.object (common f M N A B hA hB eA eB) (transfer f unitMap (common f M N A B hA hB eA eB)
      (InverseImageLineCocycle318.cocycle f N (common f M N A B hA hB eA eB)
        (rightFrame f M N A B hA hB eA eB))):=
  UnitTransferCoverIso318.iso f unitMap N (rightOpen f N B hB eB) (common f M N A B hA hB eA eB)
    (sourceFrame f N B hB eB) (rightFrame f M N A B hA hB eA eB)
    (target_cover f N B hB eB) (cover f M N A B hA hB eA eB)
end FiniteUnitTransferTensorCommon318
