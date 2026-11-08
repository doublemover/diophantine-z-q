module
public import FifthNormTensorCommon318
public import FifthNormTensorIso318
public section
noncomputable section
namespace FifthNormChosenTensorIso318
open AlgebraicGeometry CategoryTheory
open IntrinsicTensorSheaf318 FifthCompletedGlobal318 FifthChartNorm318
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (M N:Model.Modules) {α β γ:Type}
    (A:α→Model.Opens) (B:β→Model.Opens) (C:γ→Model.Opens)
    (hA:(⊤:Model.Opens)≤⨆i,A i) (hB:(⊤:Model.Opens)≤⨆j,B j)
    (hC:(⊤:Model.Opens)≤⨆k,C k)
    (eA:∀i,SheafOfModules.unit (A i).toScheme.ringCatSheaf≅M.restrict (A i).ι)
    (eB:∀j,SheafOfModules.unit (B j).toScheme.ringCatSheaf≅N.restrict (B j).ι)
    (eC:∀k,SheafOfModules.unit (C k).toScheme.ringCatSheaf≅(tensor M N).restrict (C k).ι)
abbrev family:=FifthNormTensorCommon318.common M N A B hA hB eA eB
abbrev firstFrame:=FifthNormTensorCommon318.leftFrame M N A B hA hB eA eB
abbrev secondFrame:=FifthNormTensorCommon318.rightFrame M N A B hA hB eA eB
abbrev tensorFrame:=TensorLineCocycle318.frames M N
  (fun i=>map⁻¹ᵁfamily M N A B hA hB eA eB i)
  (firstFrame M N A B hA hB eA eB) (secondFrame M N A B hA hB eA eB)
/-- The actual tensor source is retained, while its independently supplied
norm presentation is compared with the genuine common tensor-frame cover. -/
@[expose] def sourceIso:FifthNormLineObject318.object (tensor M N) C hC eC≅
    CocycleModule318.object (family M N A B hA hB eA eB) (FifthNormCocycle318.transfer
      (InverseImageLineCocycle318.cocycle map (tensor M N) (family M N A B hA hB eA eB)
        (tensorFrame M N A B hA hB eA eB))):=
  FifthNormCoverIso318.iso (tensor M N)
    (FifthLineTargetCover318.neighborhood (tensor M N) C hC eC)
    (family M N A B hA hB eA eB)
    (FifthLineTargetCover318.frame (tensor M N) C hC eC)
    (tensorFrame M N A B hA hB eA eB)
    (FifthLineTargetCover318.cover_top (tensor M N) C hC eC)
    (FifthNormTensorCommon318.cover M N A B hA hB eA eB)
/-- Multiplicativity as an actual module-sheaf isomorphism for three
independently supplied original line presentations, not a choice of labels
or an assumed Picard-group operation. -/
@[expose] def iso:FifthNormLineObject318.object (tensor M N) C hC eC≅
    tensor (FifthNormLineObject318.object M A hA eA) (FifthNormLineObject318.object N B hB eB):=
  sourceIso M N A B C hA hB hC eA eB eC≪≫
    FifthNormTensorIso318.iso M N (family M N A B hA hB eA eB)
      (firstFrame M N A B hA hB eA eB) (secondFrame M N A B hA hB eA eB)
      (FifthNormTensorCommon318.cover M N A B hA hB eA eB)≪≫
    TensorSheafFunctor318.congr
      (FifthNormTensorCommon318.leftIso M N A B hA hB eA eB).symm
      (FifthNormTensorCommon318.rightIso M N A B hA hB eA eB).symm
lemma hom_inv:(iso M N A B C hA hB hC eA eB eC).hom≫
    (iso M N A B C hA hB hC eA eB eC).inv=𝟙 _ :=(iso M N A B C hA hB hC eA eB eC).hom_inv_id
lemma inv_hom:(iso M N A B C hA hB hC eA eB eC).inv≫
    (iso M N A B C hA hB hC eA eB eC).hom=𝟙 _ :=(iso M N A B C hA hB hC eA eB eC).inv_hom_id
end FifthNormChosenTensorIso318
