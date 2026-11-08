module
public import CompletedCharacterNormLine318
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
/-- The reconstructed original source transition is exactly the pushed unit
being transferred, across the literal full preimage intersection. -/
lemma original_transition (y z:Y):
    Units.map (X.presheaf.map (homOfLE (show
      f⁻¹ᵁ(targetOpen f M A hA eA y⊓targetOpen f M A hA eA z)≤
        sourceOpen f M A hA eA y⊓sourceOpen f M A hA eA z from
          le_inf (f.preimage_mono inf_le_left) (f.preimage_mono inf_le_right))).op).hom.toMonoidHom
      ((LineFrameCocycle318.cocycle M (sourceOpen f M A hA eA) (sourceFrame f M A hA eA)).transition y z)=
      (sourceCocycle f M A hA eA).transition y z:=
  LineFrameTransitions318.restrict M (sourceOpen f M A hA eA)
    (sourceFrame f M A hA eA) y z inf_le_left inf_le_right _
end FiniteUnitTransferPresentation318
namespace CompletedCharacterNormTransition318
open AlgebraicGeometry CategoryTheory Opposite SourceTwistArithmetic318
open CompletedCharacterSchemeMaps318 CompletedCharacterGlobal318 CompletedCharacterNormLine318
set_option maxHeartbeats 450000
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
local instance mapFinite (i:Fin 4):IsFinite (completedMap i):=
  CompletedCharacterFinite318.completedMap_finite i
variable (i:Fin 4) (M:Model.Modules) {ι:Type} (A:ι→Model.Opens)
    (hA:(⊤:Model.Opens)≤⨆j,A j)
    (eA:∀j,SheafOfModules.unit (A j).toScheme.ringCatSheaf≅M.restrict (A j).ι)
abbrev sourceOpen:=FiniteUnitTransferPresentation318.sourceOpen (completedMap i) M A hA eA
abbrev sourceFrame:=FiniteUnitTransferPresentation318.sourceFrame (completedMap i) M A hA eA
/-- No source presentation is silently replaced: these are exactly the
transition units in the coefficient-module reconstruction of original M. -/
@[expose] def originalUnit (y z:Target i):
    Γ(Model,completedMap i⁻¹ᵁ(neighborhood i M A hA eA y⊓neighborhood i M A hA eA z))ˣ:=
  Units.map (Model.presheaf.map (homOfLE (show
    completedMap i⁻¹ᵁ(neighborhood i M A hA eA y⊓neighborhood i M A hA eA z)≤
      sourceOpen i M A hA eA y⊓sourceOpen i M A hA eA z from
        le_inf ((completedMap i).preimage_mono inf_le_left) ((completedMap i).preimage_mono inf_le_right))).op).hom.toMonoidHom
    ((LineFrameCocycle318.cocycle M (sourceOpen i M A hA eA) (sourceFrame i M A hA eA)).transition y z)
lemma originalUnit_eq (y z:Target i):
    originalUnit i M A hA eA y z=(sourceCocycle i M A hA eA).transition y z:=
  FiniteUnitTransferPresentation318.original_transition (completedMap i) M A hA eA y z
lemma original_norm_transition (y z:Target i):
    Units.val (α:=Γ(Target i,neighborhood i M A hA eA y⊓neighborhood i M A hA eA z))
      ((targetCocycle i M A hA eA).transition y z)=
    CompletedCharacterOpenNorm318.norm i
      (neighborhood i M A hA eA y⊓neighborhood i M A hA eA z)
      (originalUnit i M A hA eA y z):=by
  rw [originalUnit_eq]
  exact norm_original_transition i M A hA eA y z
end CompletedCharacterNormTransition318
