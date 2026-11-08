module
public import FiniteUnitTransferTensorCommon318
public import UnitTransferTensorIso318
public section
noncomputable section
namespace FiniteUnitTransferTensorIso318
open AlgebraicGeometry CategoryTheory
open IntrinsicTensorSheaf318 UnitTransferGaugeIso318 FiniteUnitTransferPresentation318
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X Y:Scheme.{u}} (f:X⟶Y) [IsFinite f]
    (unitMap:StructureUnitsSheaf318.pushedUnits f⟶StructureUnitsSheaf318.units Y)
    (M N:X.Modules) {α β γ:Type u}
    (A:α→X.Opens) (B:β→X.Opens) (C:γ→X.Opens)
    (hA:(⊤:X.Opens)≤⨆i,A i) (hB:(⊤:X.Opens)≤⨆j,B j)
    (hC:(⊤:X.Opens)≤⨆k,C k)
    (eA:∀i,SheafOfModules.unit (A i).toScheme.ringCatSheaf≅M.restrict (A i).ι)
    (eB:∀j,SheafOfModules.unit (B j).toScheme.ringCatSheaf≅N.restrict (B j).ι)
    (eC:∀k,SheafOfModules.unit (C k).toScheme.ringCatSheaf≅(tensor M N).restrict (C k).ι)
abbrev family:=FiniteUnitTransferTensorCommon318.common f M N A B hA hB eA eB
abbrev firstFrame:=FiniteUnitTransferTensorCommon318.leftFrame f M N A B hA hB eA eB
abbrev secondFrame:=FiniteUnitTransferTensorCommon318.rightFrame f M N A B hA hB eA eB
abbrev tensorFrame:=TensorLineCocycle318.frames M N
  (fun i=>f⁻¹ᵁfamily f M N A B hA hB eA eB i)
  (firstFrame f M N A B hA hB eA eB) (secondFrame f M N A B hA hB eA eB)
/-- The actual tensor source is retained, while its independently supplied
norm presentation is compared with the genuine common tensor-frame cover. -/
@[expose] def sourceIso:FiniteUnitTransferLine318.object f (tensor M N) C hC eC unitMap≅
    CocycleModule318.object (family f M N A B hA hB eA eB) (transfer f unitMap (family f M N A B hA hB eA eB)
      (InverseImageLineCocycle318.cocycle f (tensor M N) (family f M N A B hA hB eA eB)
        (tensorFrame f M N A B hA hB eA eB))):=
  UnitTransferCoverIso318.iso f unitMap (tensor M N)
    (targetOpen f (tensor M N) C hC eC)
    (family f M N A B hA hB eA eB)
    (sourceFrame f (tensor M N) C hC eC)
    (tensorFrame f M N A B hA hB eA eB)
    (target_cover f (tensor M N) C hC eC)
    (FiniteUnitTransferTensorCommon318.cover f M N A B hA hB eA eB)
/-- Multiplicativity as an actual module-sheaf isomorphism for three
independently supplied original line presentations, not a choice of labels
or an assumed Picard-group operation. -/
@[expose] def iso:FiniteUnitTransferLine318.object f (tensor M N) C hC eC unitMap≅
    tensor (FiniteUnitTransferLine318.object f M A hA eA unitMap) (FiniteUnitTransferLine318.object f N B hB eB unitMap):=
  sourceIso f unitMap M N A B C hA hB hC eA eB eC≪≫
    UnitTransferTensorIso318.iso f unitMap M N (family f M N A B hA hB eA eB)
      (firstFrame f M N A B hA hB eA eB) (secondFrame f M N A B hA hB eA eB)
      (FiniteUnitTransferTensorCommon318.cover f M N A B hA hB eA eB)≪≫
    TensorSheafFunctor318.congr
      (FiniteUnitTransferTensorCommon318.leftIso f unitMap M N A B hA hB eA eB).symm
      (FiniteUnitTransferTensorCommon318.rightIso f unitMap M N A B hA hB eA eB).symm
lemma hom_inv:(iso f unitMap M N A B C hA hB hC eA eB eC).hom≫
    (iso f unitMap M N A B C hA hB hC eA eB eC).inv=𝟙 _ :=(iso f unitMap M N A B C hA hB hC eA eB eC).hom_inv_id
lemma inv_hom:(iso f unitMap M N A B C hA hB hC eA eB eC).inv≫
    (iso f unitMap M N A B C hA hB hC eA eB eC).hom=𝟙 _ :=(iso f unitMap M N A B C hA hB hC eA eB eC).inv_hom_id
end FiniteUnitTransferTensorIso318
