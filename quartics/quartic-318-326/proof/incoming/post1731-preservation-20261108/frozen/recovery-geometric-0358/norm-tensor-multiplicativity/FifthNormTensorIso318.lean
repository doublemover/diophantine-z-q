module
public import FifthNormTensorCocycle318
public import CocycleTensorIso318
public import FifthNormCoverIso318
public section
noncomputable section
namespace FifthNormTensorIso318
open AlgebraicGeometry CategoryTheory
open IntrinsicTensorSheaf318 FifthCompletedGlobal318 FifthChartNorm318
set_option maxHeartbeats 550000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (M N:Model.Modules) {ι:Type} (U:ι→Target.Opens)
    (em:∀i,SheafOfModules.unit (map⁻¹ᵁU i).toScheme.ringCatSheaf≅M.restrict (map⁻¹ᵁU i).ι)
    (en:∀i,SheafOfModules.unit (map⁻¹ᵁU i).toScheme.ringCatSheaf≅N.restrict (map⁻¹ᵁU i).ι)
/-- Genuine fixed-cover norm tensor comparison. The source is the norm of
the actual source tensor; the target is the actual tensor of the two norm
sheaves. The comparison is not only an equality of transition labels. -/
@[expose] def iso (hc:(⊤:Target.Opens)≤⨆i,U i):
    CocycleModule318.object U (FifthNormCocycle318.transfer
      (InverseImageLineCocycle318.cocycle map (tensor M N) U
        (TensorLineCocycle318.frames M N (fun i=>map⁻¹ᵁU i) em en)))≅
    tensor (CocycleModule318.object U (FifthNormCocycle318.transfer
      (InverseImageLineCocycle318.cocycle map M U em)))
      (CocycleModule318.object U (FifthNormCocycle318.transfer
        (InverseImageLineCocycle318.cocycle map N U en))):=
  CocycleEqualityTransport318.iso U (FifthNormTensorCocycle318.norm_cocycle M N U em en)≪≫
    (CocycleTensorIso318.iso U _ _ hc).symm
lemma hom_inv (hc:(⊤:Target.Opens)≤⨆i,U i):
    (iso M N U em en hc).hom≫(iso M N U em en hc).inv=𝟙 _ :=(iso M N U em en hc).hom_inv_id
lemma inv_hom (hc:(⊤:Target.Opens)≤⨆i,U i):
    (iso M N U em en hc).inv≫(iso M N U em en hc).hom=𝟙 _ :=(iso M N U em en hc).inv_hom_id
end FifthNormTensorIso318
