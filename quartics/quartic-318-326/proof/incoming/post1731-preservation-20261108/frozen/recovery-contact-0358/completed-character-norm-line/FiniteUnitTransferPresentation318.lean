module
public import FiniteLineTargetCover318
public import InverseImageLineCocycle318
public import LineFrameReconstructionIso318
public section
noncomputable section
namespace FiniteUnitTransferPresentation318
open AlgebraicGeometry CategoryTheory Opposite
set_option maxHeartbeats 450000
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X Y:Scheme.{u}} (f:X⟶Y) [IsFinite f] (M:X.Modules)
    {ι:Type u} (A:ι→X.Opens) (hA:(⊤:X.Opens)≤⨆i,A i)
    (eA:∀i,SheafOfModules.unit (A i).toScheme.ringCatSheaf≅M.restrict (A i).ι)
abbrev targetOpen:=FiniteLineTargetCover318.neighborhood f M A hA eA
@[expose] def sourceOpen (y:Y):X.Opens:=f⁻¹ᵁtargetOpen f M A hA eA y
@[expose] def sourceFrame (y:Y):SheafOfModules.unit (sourceOpen f M A hA eA y).toScheme.ringCatSheaf≅
    M.restrict (sourceOpen f M A hA eA y).ι:=FiniteLineTargetCover318.frame f M A hA eA y
lemma target_cover:(⊤:Y.Opens)≤⨆y,targetOpen f M A hA eA y:=
  FiniteLineTargetCover318.cover_top f M A hA eA
lemma source_cover:(⊤:X.Opens)≤⨆y,sourceOpen f M A hA eA y:=
  FiniteLineTargetCover318.preimage_cover_top f M A hA eA
/-- The original source module is actually reconstructed from the genuine
whole-inverse-image frames used below. -/
@[expose] def sourceIso:M≅CocycleModule318.object (sourceOpen f M A hA eA)
    (LineFrameCocycle318.cocycle M (sourceOpen f M A hA eA) (sourceFrame f M A hA eA)):=
  LineFrameReconstructionIso318.iso M (sourceOpen f M A hA eA)
    (sourceFrame f M A hA eA) (source_cover f M A hA eA)
lemma source_hom_inv:(sourceIso f M A hA eA).hom≫(sourceIso f M A hA eA).inv=𝟙 M:=
  (sourceIso f M A hA eA).hom_inv_id
lemma source_inv_hom:(sourceIso f M A hA eA).inv≫(sourceIso f M A hA eA).hom=𝟙 _:=
  (sourceIso f M A hA eA).inv_hom_id
lemma source_coordinate (y:Y):
    (sourceIso f M A hA eA).hom≫CocycleModule318.coefficient (sourceOpen f M A hA eA)
      (LineFrameCocycle318.cocycle M (sourceOpen f M A hA eA) (sourceFrame f M A hA eA)) y=
      LineFrameAdjunction318.coordinate M (sourceOpen f M A hA eA y) (sourceFrame f M A hA eA y):=
  LineFrameReconstructionIso318.hom_coefficient M _ _ _ y
/-- Actual source transitions on each complete target-overlap inverse image. -/
@[expose] def sourceCocycle:=InverseImageLineCocycle318.cocycle f M
  (targetOpen f M A hA eA) (sourceFrame f M A hA eA)
variable (unitMap:StructureUnitsSheaf318.pushedUnits f⟶StructureUnitsSheaf318.units Y)
/-- Transfer through the specified actual unit-sheaf morphism. For the concrete
character consumer this is the already constructed regular norm. -/
@[expose] def targetCocycle:=UnitTransitionCocycle318.map unitMap.hom (sourceCocycle f M A hA eA)
lemma transition (y z:Y):
    (targetCocycle f M A hA eA unitMap).transition y z=
      unitMap.hom.app (op (targetOpen f M A hA eA y⊓targetOpen f M A hA eA z))
        (LineFrameTransitions318.scalar M (sourceOpen f M A hA eA) (sourceFrame f M A hA eA)
          y z (f⁻¹ᵁ(targetOpen f M A hA eA y⊓targetOpen f M A hA eA z))
          (f.preimage_mono inf_le_left) (f.preimage_mono inf_le_right)):=rfl
end FiniteUnitTransferPresentation318
