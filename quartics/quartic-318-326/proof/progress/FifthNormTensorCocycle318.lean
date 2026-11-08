module
public import TensorInverseImageCocycle318
public import FifthNormCoverIso318
public section
noncomputable section
namespace FifthNormTensorCocycle318
open AlgebraicGeometry CategoryTheory
open IntrinsicTensorSheaf318 FifthCompletedGlobal318 FifthChartNorm318
set_option maxHeartbeats 550000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (M N:Model.Modules) {ι:Type} (U:ι→Target.Opens)
    (em:∀i,SheafOfModules.unit (map⁻¹ᵁU i).toScheme.ringCatSheaf≅M.restrict (map⁻¹ᵁU i).ι)
    (en:∀i,SheafOfModules.unit (map⁻¹ᵁU i).toScheme.ringCatSheaf≅N.restrict (map⁻¹ᵁU i).ι)
/-- Product compatibility of the actual regular-unit norm, applied to
transitions derived from the actual source tensor sheaf and original frames. -/
lemma norm_cocycle:
    FifthNormCocycle318.transfer (InverseImageLineCocycle318.cocycle map (tensor M N) U
      (TensorLineCocycle318.frames M N (fun i=>map⁻¹ᵁU i) em en))=
    UnitCocycleProduct318.product
      (FifthNormCocycle318.transfer (InverseImageLineCocycle318.cocycle map M U em))
      (FifthNormCocycle318.transfer (InverseImageLineCocycle318.cocycle map N U en)):=by
  rw [TensorInverseImageCocycle318.cocycle_eq]
  exact UnitCocycleProduct318.map_product FifthSheafNorm318.norm.hom _ _
end FifthNormTensorCocycle318
