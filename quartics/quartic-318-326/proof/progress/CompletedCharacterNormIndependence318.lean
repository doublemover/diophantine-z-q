module
public import FiniteUnitTransferSourceIso318
public import CompletedCharacterNormLine318
public section
noncomputable section
namespace CompletedCharacterNormIndependence318
open AlgebraicGeometry CategoryTheory SourceTwistArithmetic318
open CompletedCharacterSchemeMaps318 CompletedCharacterGlobal318 CompletedCharacterNormLine318
set_option maxHeartbeats 450000
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
local instance mapFinite (i:Fin 4):IsFinite (completedMap i):=
  CompletedCharacterFinite318.completedMap_finite i
variable (i:Fin 4) {M N:Model.Modules} (e:M≅N) {α β:Type}
    (A:α→Model.Opens) (B:β→Model.Opens)
    (hA:(⊤:Model.Opens)≤⨆j,A j) (hB:(⊤:Model.Opens)≤⨆k,B k)
    (eA:∀j,SheafOfModules.unit (A j).toScheme.ringCatSheaf≅M.restrict (A j).ι)
    (eB:∀k,SheafOfModules.unit (B k).toScheme.ringCatSheaf≅N.restrict (B k).ι)
/-- All four unchanged completed maps retain the exact actual unit norm and
both independently chosen source presentations in their target comparison. -/
@[expose] def iso:CompletedCharacterNormLine318.object i M A hA eA≅
    CompletedCharacterNormLine318.object i N B hB eB:=
  FiniteUnitTransferSourceIso318.iso (completedMap i) (CompletedCharacterSheafNorm318.norm i)
    e A B hA hB eA eB
lemma hom_inv:(iso i e A B hA hB eA eB).hom≫(iso i e A B hA hB eA eB).inv=𝟙 _ :=
  (iso i e A B hA hB eA eB).hom_inv_id
lemma inv_hom:(iso i e A B hA hB eA eB).inv≫(iso i e A B hA hB eA eB).hom=𝟙 _ :=
  (iso i e A B hA hB eA eB).inv_hom_id
/-- Literal framed-line consumer, with no equality of the two cover records. -/
@[expose] def lineIso (i:Fin 4) {L K:LineSheafClass318.Line Model} (e:L.object≅K.object):
    (CompletedCharacterNormLine318.line i L).object≅(CompletedCharacterNormLine318.line i K).object:=
  iso i e L.opens K.opens L.cover K.cover L.frame K.frame
lemma line_hom_inv (i:Fin 4) {L K:LineSheafClass318.Line Model} (e:L.object≅K.object):
    (lineIso i e).hom≫(lineIso i e).inv=𝟙 _ :=(lineIso i e).hom_inv_id
lemma line_inv_hom (i:Fin 4) {L K:LineSheafClass318.Line Model} (e:L.object≅K.object):
    (lineIso i e).inv≫(lineIso i e).hom=𝟙 _ :=(lineIso i e).inv_hom_id
end CompletedCharacterNormIndependence318
