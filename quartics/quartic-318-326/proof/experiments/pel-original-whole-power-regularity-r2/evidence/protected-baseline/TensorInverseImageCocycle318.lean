module
public import TensorLineCocycle318
public import InverseImageLineCocycle318
public section
noncomputable section
namespace TensorInverseImageCocycle318
open AlgebraicGeometry CategoryTheory
open IntrinsicTensorSheaf318
set_option maxHeartbeats 550000
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
variable {X Y:Scheme.{u}} (f:X⟶Y) (M N:X.Modules) {ι:Type v} (U:ι→Y.Opens)
    (em:∀i,SheafOfModules.unit (f⁻¹ᵁU i).toScheme.ringCatSheaf≅M.restrict (f⁻¹ᵁU i).ι)
    (en:∀i,SheafOfModules.unit (f⁻¹ᵁU i).toScheme.ringCatSheaf≅N.restrict (f⁻¹ᵁU i).ι)
/-- Genuine whole-preimage tensor frames give precisely the product of the
two original pushed-unit cocycles on complete target intersections. -/
lemma cocycle_eq:
    InverseImageLineCocycle318.cocycle f (tensor M N) U
      (TensorLineCocycle318.frames M N (fun i=>f⁻¹ᵁU i) em en)=
    UnitCocycleProduct318.product (InverseImageLineCocycle318.cocycle f M U em)
      (InverseImageLineCocycle318.cocycle f N U en):=by
  apply UnitTransitionCocycle318.Cocycle.ext
  intro i j
  exact TensorLineCocycle318.scalar_product M N (fun i=>f⁻¹ᵁU i) em en i j
    (f⁻¹ᵁ(U i⊓U j)) (f.preimage_mono inf_le_left) (f.preimage_mono inf_le_right)
end TensorInverseImageCocycle318
