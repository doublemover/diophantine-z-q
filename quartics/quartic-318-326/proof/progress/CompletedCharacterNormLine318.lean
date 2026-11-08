module
public import FiniteUnitTransferLine318
public import CompletedCharacterSheafNorm318
public import LineSheafClass318
public section
noncomputable section
namespace CompletedCharacterNormLine318
open AlgebraicGeometry CategoryTheory Opposite SourceTwistArithmetic318
open CompletedCharacterSchemeMaps318 CompletedCharacterGlobal318
set_option maxHeartbeats 450000
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
abbrev Model:=ContactGlobalSmooth318.Model units
local instance mapFinite (i:Fin 4):IsFinite (completedMap i):=
  CompletedCharacterFinite318.completedMap_finite i
variable (i:Fin 4) (M:Model.Modules) {ι:Type} (A:ι→Model.Opens)
    (hA:(⊤:Model.Opens)≤⨆j,A j)
    (eA:∀j,SheafOfModules.unit (A j).toScheme.ringCatSheaf≅M.restrict (A j).ι)
abbrev neighborhood:=FiniteUnitTransferPresentation318.targetOpen (completedMap i) M A hA eA
abbrev sourceCocycle:=FiniteUnitTransferPresentation318.sourceCocycle (completedMap i) M A hA eA
abbrev targetCocycle:=FiniteUnitTransferPresentation318.targetCocycle (completedMap i) M A hA eA
  (CompletedCharacterSheafNorm318.norm i)
/-- The genuine norm-line object for each of the four unchanged completed
quotient maps, formed from the actual all-open regular unit norm. -/
@[expose] def object:(Target i).Modules:=FiniteUnitTransferLine318.object
  (completedMap i) M A hA eA (CompletedCharacterSheafNorm318.norm i)
@[expose] def frame (y:Target i):
    SheafOfModules.unit (neighborhood i M A hA eA y).toScheme.ringCatSheaf≅
      (object i M A hA eA).restrict (neighborhood i M A hA eA y).ι:=
  FiniteUnitTransferLine318.frame (completedMap i) M A hA eA (CompletedCharacterSheafNorm318.norm i) y
lemma cover:(⊤:(Target i).Opens)≤⨆y,neighborhood i M A hA eA y:=
  FiniteUnitTransferPresentation318.target_cover (completedMap i) M A hA eA
lemma locallyFree:(object i M A hA eA).IsLocallyFree:=
  FiniteUnitTransferLine318.locallyFree (completedMap i) M A hA eA (CompletedCharacterSheafNorm318.norm i)
lemma frame_hom_inv (y:Target i):(frame i M A hA eA y).hom≫(frame i M A hA eA y).inv=𝟙 _ :=
  (frame i M A hA eA y).hom_inv_id
lemma frame_inv_hom (y:Target i):(frame i M A hA eA y).inv≫(frame i M A hA eA y).hom=𝟙 _ :=
  (frame i M A hA eA y).inv_hom_id
/-- Exact original source-module reconstruction, not an assumed source alias. -/
@[expose] def sourceIso:=FiniteUnitTransferPresentation318.sourceIso (completedMap i) M A hA eA
lemma original_target_transitions:
    LineFrameCocycle318.cocycle (object i M A hA eA) (neighborhood i M A hA eA)
      (frame i M A hA eA)=targetCocycle i M A hA eA:=
  FiniteUnitTransferLine318.original_transitions (completedMap i) M A hA eA
    (CompletedCharacterSheafNorm318.norm i)
/-- Every complete target-overlap transition is the genuine regular norm
of the original whole-inverse-image source transition. -/
lemma norm_original_transition (y z:Target i):
    Units.val (α:=Γ(Target i,neighborhood i M A hA eA y⊓neighborhood i M A hA eA z))
      ((targetCocycle i M A hA eA).transition y z)=
    CompletedCharacterOpenNorm318.norm i
      (neighborhood i M A hA eA y⊓neighborhood i M A hA eA z)
      (Units.val (α:=Γ(Model,completedMap i⁻¹ᵁ(neighborhood i M A hA eA y⊓neighborhood i M A hA eA z)))
        ((sourceCocycle i M A hA eA).transition y z)):=
  CompletedCharacterSheafNorm318.original_value i _ _
/-- The actual framed target line for each supplied original source line.
No presentation-independent class map is asserted by this object producer. -/
@[expose] def line (i:Fin 4) (L:LineSheafClass318.Line Model):LineSheafClass318.Line (Target i) where
  object:=object i L.object L.opens L.cover L.frame
  Index:=Target i
  opens:=neighborhood i L.object L.opens L.cover L.frame
  cover:=cover i L.object L.opens L.cover L.frame
  frame:=frame i L.object L.opens L.cover L.frame
end CompletedCharacterNormLine318
