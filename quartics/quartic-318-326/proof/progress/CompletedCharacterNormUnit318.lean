module
public import FiniteUnitTransferUnit318
public import CompletedCharacterNormIndependence318
public section
noncomputable section
namespace CompletedCharacterNormUnit318
open AlgebraicGeometry CategoryTheory SourceTwistArithmetic318
open CompletedCharacterSchemeMaps318 CompletedCharacterGlobal318 CompletedCharacterNormLine318
set_option maxHeartbeats 450000
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
local instance mapFinite (i:Fin 4):IsFinite (completedMap i):=
  CompletedCharacterFinite318.completedMap_finite i
variable (i:Fin 4) (M:Model.Modules) (e:M≅SheafOfModules.unit Model.ringCatSheaf)
    {α:Type} (A:α→Model.Opens) (hA:(⊤:Model.Opens)≤⨆j,A j)
    (eA:∀j,SheafOfModules.unit (A j).toScheme.ringCatSheaf≅M.restrict (A j).ι)
/-- Actual original target structure module for each of the four unchanged
norm maps, from any genuine trivialization of the original source line. -/
@[expose] def iso:CompletedCharacterNormLine318.object i M A hA eA≅
    SheafOfModules.unit (Target i).ringCatSheaf:=
  FiniteUnitTransferUnit318.iso (completedMap i) (CompletedCharacterSheafNorm318.norm i)
    M e A hA eA
lemma hom_inv:(iso i M e A hA eA).hom≫(iso i M e A hA eA).inv=𝟙 _ :=
  (iso i M e A hA eA).hom_inv_id
lemma inv_hom:(iso i M e A hA eA).inv≫(iso i M e A hA eA).hom=𝟙 _ :=
  (iso i M e A hA eA).inv_hom_id
@[expose] def lineIso (i:Fin 4) (L:LineSheafClass318.Line Model)
    (e:L.object≅SheafOfModules.unit Model.ringCatSheaf):
    (CompletedCharacterNormLine318.line i L).object≅SheafOfModules.unit (Target i).ringCatSheaf:=
  iso i L.object e L.opens L.cover L.frame
end CompletedCharacterNormUnit318
