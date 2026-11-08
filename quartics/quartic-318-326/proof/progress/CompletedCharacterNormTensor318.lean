module
public import FiniteUnitTransferTensorIso318
public import CompletedCharacterNormIndependence318
public import LineSheafTensor318
public section
noncomputable section
namespace CompletedCharacterNormTensor318
open AlgebraicGeometry CategoryTheory SourceTwistArithmetic318 IntrinsicTensorSheaf318
open CompletedCharacterSchemeMaps318 CompletedCharacterGlobal318 CompletedCharacterNormLine318
set_option maxHeartbeats 600000
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
local instance mapFinite (i:Fin 4):IsFinite (completedMap i):=
  CompletedCharacterFinite318.completedMap_finite i
variable (i:Fin 4) (M N:Model.Modules) {α β γ:Type}
    (A:α→Model.Opens) (B:β→Model.Opens) (C:γ→Model.Opens)
    (hA:(⊤:Model.Opens)≤⨆j,A j) (hB:(⊤:Model.Opens)≤⨆j,B j)
    (hC:(⊤:Model.Opens)≤⨆j,C j)
    (eA:∀j,SheafOfModules.unit (A j).toScheme.ringCatSheaf≅M.restrict (A j).ι)
    (eB:∀j,SheafOfModules.unit (B j).toScheme.ringCatSheaf≅N.restrict (B j).ι)
    (eC:∀j,SheafOfModules.unit (C j).toScheme.ringCatSheaf≅(tensor M N).restrict (C j).ι)
/-- The genuine norm of the original tensor sheaf, for each unchanged
completed character map, is isomorphic to the actual tensor of the two
original norm sheaves. All three covering presentations are independent. -/
@[expose] def iso:CompletedCharacterNormLine318.object i (tensor M N) C hC eC≅
    tensor (CompletedCharacterNormLine318.object i M A hA eA)
      (CompletedCharacterNormLine318.object i N B hB eB):=
  FiniteUnitTransferTensorIso318.iso (completedMap i) (CompletedCharacterSheafNorm318.norm i)
    M N A B C hA hB hC eA eB eC
lemma hom_inv:(iso i M N A B C hA hB hC eA eB eC).hom≫
    (iso i M N A B C hA hB hC eA eB eC).inv=𝟙 _ :=
  (iso i M N A B C hA hB hC eA eB eC).hom_inv_id
lemma inv_hom:(iso i M N A B C hA hB hC eA eB eC).inv≫
    (iso i M N A B C hA hB hC eA eB eC).hom=𝟙 _ :=
  (iso i M N A B C hA hB hC eA eB eC).inv_hom_id
/-- Exact existing framed-line tensor endpoints, not an equality assigned
on labels and not a monoidal-coherence assertion. -/
@[expose] def lineIso (i:Fin 4) (L N:LineSheafClass318.Line Model):
    (CompletedCharacterNormLine318.line i (LineSheafTensor318.line L N)).object≅
      (LineSheafTensor318.line (CompletedCharacterNormLine318.line i L)
        (CompletedCharacterNormLine318.line i N)).object:=
  iso i L.object N.object L.opens N.opens (LineSheafTensor318.line L N).opens
    L.cover N.cover (LineSheafTensor318.line L N).cover
    L.frame N.frame (LineSheafTensor318.line L N).frame
lemma line_hom_inv (i:Fin 4) (L N:LineSheafClass318.Line Model):
    (lineIso i L N).hom≫(lineIso i L N).inv=𝟙 _ :=(lineIso i L N).hom_inv_id
lemma line_inv_hom (i:Fin 4) (L N:LineSheafClass318.Line Model):
    (lineIso i L N).inv≫(lineIso i L N).hom=𝟙 _ :=(lineIso i L N).inv_hom_id
end CompletedCharacterNormTensor318
