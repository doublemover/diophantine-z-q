module
public import LineFrameCoefficientCompatibility318
public import CocycleReconstructionCriterion318
public section
noncomputable section
namespace LineFrameCocycleReconstruction318
open AlgebraicGeometry CategoryTheory
set_option maxHeartbeats 550000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X:Scheme.{u}} (M:X.Modules) {ι:Type u} (U:ι→X.Opens)
    (frames:∀i,SheafOfModules.unit (U i).toScheme.ringCatSheaf≅M.restrict (U i).ι)
abbrev cocycle:=LineFrameCoefficientCompatibility318.cocycle M U frames
/-- The actual original line's map to its actual extracted coefficient module. -/
@[expose] def map:M⟶CocycleModule318.object U (cocycle M U frames):=
  CocycleModule318.lift U (cocycle M U frames)
    (LineFrameCoefficientCompatibility318.coefficient M U frames)
    (LineFrameCoefficientCompatibility318.compatible M U frames)
lemma map_coefficient (i:ι):
    map M U frames≫CocycleModule318.coefficient U (cocycle M U frames) i=
      LineFrameAdjunction318.coordinate M (U i) (frames i):=
  CocycleModule318.lift_coefficient _ _ _ _ i
lemma map_projection (i:ι):
    (Scheme.Modules.restrictFunctor (U i).ι).map (map M U frames)≫
      CocycleReconstructionCriterion318.projection U (cocycle M U frames) i=(frames i).inv:=
  (CocycleReconstructionCriterion318.lift_projection _ _ _ _ i).trans
    (LineFrameAdjunction318.transpose M (U i) (frames i))
lemma unique (g:M⟶CocycleModule318.object U (cocycle M U frames))
    (h:∀i,g≫CocycleModule318.coefficient U (cocycle M U frames) i=
      LineFrameAdjunction318.coordinate M (U i) (frames i)):g=map M U frames:=
  CocycleModule318.hom_ext _ _ _ _ (fun i=>(h i).trans (map_coefficient M U frames i).symm)
/-- Explicit remaining local-projection criterion. The actual cocycle-frame
producer must discharge hp before this yields reconstruction as an isomorphism. -/
lemma isIso_of_projection (hc:(⊤:X.Opens)≤⨆i,U i)
    (hp:∀i,IsIso (CocycleReconstructionCriterion318.projection U (cocycle M U frames) i)):
    IsIso (map M U frames):=by
  apply CocycleReconstructionCriterion318.lift_isIso _ _ _ _ hc hp
  intro i
  change IsIso (((Scheme.Modules.restrictAdjunction (U i).ι).homEquiv M
    (SheafOfModules.unit (U i).toScheme.ringCatSheaf)).symm
      (LineFrameAdjunction318.coordinate M (U i) (frames i)))
  rw [LineFrameAdjunction318.transpose]
  infer_instance
end LineFrameCocycleReconstruction318
