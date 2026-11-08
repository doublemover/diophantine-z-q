module
public import TensorInverseImageCocycle318
public import CocycleTensorIso318
public import FiniteUnitTransferSourceIso318
public section
noncomputable section
namespace UnitTransferTensorIso318
open AlgebraicGeometry CategoryTheory IntrinsicTensorSheaf318 UnitTransferGaugeIso318
set_option maxHeartbeats 600000
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X Y:Scheme.{u}} (f:X⟶Y)
    (unitMap:StructureUnitsSheaf318.pushedUnits f⟶StructureUnitsSheaf318.units Y)
    (M N:X.Modules) {ι:Type u} (U:ι→Y.Opens)
    (em:∀i,SheafOfModules.unit (f⁻¹ᵁU i).toScheme.ringCatSheaf≅M.restrict (f⁻¹ᵁU i).ι)
    (en:∀i,SheafOfModules.unit (f⁻¹ᵁU i).toScheme.ringCatSheaf≅N.restrict (f⁻¹ᵁU i).ι)
/-- The actual original tensor-frame transitions transfer multiplicatively
through the specified genuine morphism of sheaves of units. -/
lemma tensor_cocycle:
    transfer f unitMap U (InverseImageLineCocycle318.cocycle f (tensor M N) U
      (TensorLineCocycle318.frames M N (fun i=>f⁻¹ᵁU i) em en))=
    UnitCocycleProduct318.product
      (transfer f unitMap U (InverseImageLineCocycle318.cocycle f M U em))
      (transfer f unitMap U (InverseImageLineCocycle318.cocycle f N U en)):=by
  rw [TensorInverseImageCocycle318.cocycle_eq]
  exact UnitCocycleProduct318.map_product unitMap.hom _ _
/-- Actual fixed-cover sheaf comparison, not only transition equality. -/
@[expose] def iso (hc:(⊤:Y.Opens)≤⨆i,U i):
    CocycleModule318.object U (transfer f unitMap U
      (InverseImageLineCocycle318.cocycle f (tensor M N) U
        (TensorLineCocycle318.frames M N (fun i=>f⁻¹ᵁU i) em en)))≅
    tensor (CocycleModule318.object U (transfer f unitMap U
      (InverseImageLineCocycle318.cocycle f M U em)))
      (CocycleModule318.object U (transfer f unitMap U
        (InverseImageLineCocycle318.cocycle f N U en))):=
  CocycleEqualityTransport318.iso U (tensor_cocycle f unitMap M N U em en)≪≫
    (CocycleTensorIso318.iso U _ _ hc).symm
lemma hom_inv (hc:(⊤:Y.Opens)≤⨆i,U i):
    (iso f unitMap M N U em en hc).hom≫(iso f unitMap M N U em en hc).inv=𝟙 _ :=
  (iso f unitMap M N U em en hc).hom_inv_id
lemma inv_hom (hc:(⊤:Y.Opens)≤⨆i,U i):
    (iso f unitMap M N U em en hc).inv≫(iso f unitMap M N U em en hc).hom=𝟙 _ :=
  (iso f unitMap M N U em en hc).inv_hom_id
end UnitTransferTensorIso318
