module
public import CompletedCharacterPulledCocycle318
public import LinePullbackTransitions318
public import LineSheafPullback318
public section
noncomputable section
namespace CompletedCharacterNormPullback318
open AlgebraicGeometry CategoryTheory SourceTwistArithmetic318
open CompletedCharacterSchemeMaps318 CompletedCharacterGlobal318 CompletedCharacterNormLine318
open UnitTransferGaugeIso318 FiniteUnitTransferPresentation318
set_option maxHeartbeats 600000
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
local instance mapFinite (i:Fin 4):IsFinite (completedMap i):=
  CompletedCharacterFinite318.completedMap_finite i
variable (i:Fin 4) (M:(Target i).Modules) {ι:Type} (U:ι→(Target i).Opens)
    (em:∀j,SheafOfModules.unit (U j).toScheme.ringCatSheaf≅M.restrict (U j).ι)
    (hU:(⊤:(Target i).Opens)≤⨆j,U j)
/-- The whole-overlap transitions extracted from the literal module-sheaf
pullback and canonical actual frames, with no remaining coherence premise. -/
lemma cocycle_eq:
    InverseImageLineCocycle318.cocycle (completedMap i) ((Scheme.Modules.pullback (completedMap i)).obj M) U
      (fun j=>LinePullbackFrames318.frame (completedMap i) M (U j) (em j))=
    CompletedCharacterPulledCocycle318.pullback i U (LineFrameCocycle318.cocycle M U em):=
  LinePullbackTransitions318.cocycle (completedMap i) M U em
@[expose] def fixedIso:
    CocycleModule318.object U (transfer (completedMap i) (CompletedCharacterSheafNorm318.norm i) U
      (InverseImageLineCocycle318.cocycle (completedMap i) ((Scheme.Modules.pullback (completedMap i)).obj M) U
        (fun j=>LinePullbackFrames318.frame (completedMap i) M (U j) (em j))))≅
    FramedLineTensorPower318.object M 8:=
  CocycleEqualityTransport318.iso U (congrArg
    (transfer (completedMap i) (CompletedCharacterSheafNorm318.norm i) U) (cocycle_eq i M U em))≪≫
    CompletedCharacterPulledCocycle318.iso i U M em hU
variable {α:Type} (A:α→Model.Opens) (hA:(⊤:Model.Opens)≤⨆j,A j)
    (eA:∀j,SheafOfModules.unit (A j).toScheme.ringCatSheaf≅
      ((Scheme.Modules.pullback (completedMap i)).obj M).restrict (A j).ι)
/-- The unchanged norm of the literal source pullback, with any independent
original source covering presentation, is the actual target eighth tensor. -/
@[expose] def iso:
    CompletedCharacterNormLine318.object i ((Scheme.Modules.pullback (completedMap i)).obj M) A hA eA≅
    FramedLineTensorPower318.object M 8:=
  UnitTransferCoverIso318.iso (completedMap i) (CompletedCharacterSheafNorm318.norm i)
    ((Scheme.Modules.pullback (completedMap i)).obj M)
    (targetOpen (completedMap i) ((Scheme.Modules.pullback (completedMap i)).obj M) A hA eA) U
    (sourceFrame (completedMap i) ((Scheme.Modules.pullback (completedMap i)).obj M) A hA eA)
    (fun j=>LinePullbackFrames318.frame (completedMap i) M (U j) (em j))
    (target_cover (completedMap i) ((Scheme.Modules.pullback (completedMap i)).obj M) A hA eA) hU≪≫
    fixedIso i M U em hU
lemma hom_inv:(iso i M U em hU A hA eA).hom≫(iso i M U em hU A hA eA).inv=𝟙 _ :=
  (iso i M U em hU A hA eA).hom_inv_id
lemma inv_hom:(iso i M U em hU A hA eA).inv≫(iso i M U em hU A hA eA).hom=𝟙 _ :=
  (iso i M U em hU A hA eA).inv_hom_id
@[expose] def lineIso (i:Fin 4) (L:LineSheafClass318.Line (Target i)):
    (CompletedCharacterNormLine318.line i (LineSheafPullback318.line (completedMap i) L)).object≅
      FramedLineTensorPower318.object L.object 8:=
  iso i L.object L.opens L.frame L.cover
    (LineSheafPullback318.line (completedMap i) L).opens
    (LineSheafPullback318.line (completedMap i) L).cover
    (LineSheafPullback318.line (completedMap i) L).frame
lemma line_hom_inv (i:Fin 4) (L:LineSheafClass318.Line (Target i)):
    (lineIso i L).hom≫(lineIso i L).inv=𝟙 _ :=(lineIso i L).hom_inv_id
lemma line_inv_hom (i:Fin 4) (L:LineSheafClass318.Line (Target i)):
    (lineIso i L).inv≫(lineIso i L).hom=𝟙 _ :=(lineIso i L).inv_hom_id
end CompletedCharacterNormPullback318
