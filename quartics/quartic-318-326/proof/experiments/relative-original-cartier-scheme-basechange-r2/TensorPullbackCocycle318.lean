module
public import LinePullbackTransitions318
public import TensorLineCocycle318
public import FramedLineCocycleIso318
public section
noncomputable section
namespace TensorPullbackCocycle318
open AlgebraicGeometry CategoryTheory
set_option maxHeartbeats 600000
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X Y : Scheme.{u}} (f : X ⟶ Y) {ι : Type u} (U : ι → Y.Opens)

/-- Equality of original transitions on full inverse-image intersections gives
equality on the actual source intersections. No smaller common open is used. -/
lemma source_cocycle_eq (M N : X.Modules)
    (em : ∀ i, SheafOfModules.unit (f ⁻¹ᵁ U i).toScheme.ringCatSheaf ≅
      M.restrict (f ⁻¹ᵁ U i).ι)
    (en : ∀ i, SheafOfModules.unit (f ⁻¹ᵁ U i).toScheme.ringCatSheaf ≅
      N.restrict (f ⁻¹ᵁ U i).ι)
    (h : InverseImageLineCocycle318.cocycle f M U em =
      InverseImageLineCocycle318.cocycle f N U en) :
    LineFrameCocycle318.cocycle M (fun i => f ⁻¹ᵁ U i) em =
      LineFrameCocycle318.cocycle N (fun i => f ⁻¹ᵁ U i) en := by
  apply UnitTransitionCocycle318.Cocycle.ext
  intro i j
  change LineFrameTransitions318.scalar M (fun i => f ⁻¹ᵁ U i) em i j
      ((f ⁻¹ᵁ U i) ⊓ (f ⁻¹ᵁ U j)) inf_le_left inf_le_right =
    LineFrameTransitions318.scalar N (fun i => f ⁻¹ᵁ U i) en i j
      ((f ⁻¹ᵁ U i) ⊓ (f ⁻¹ᵁ U j)) inf_le_left inf_le_right
  have hij := congrArg (fun c => c.transition i j) h
  change LineFrameTransitions318.scalar M (fun i => f ⁻¹ᵁ U i) em i j
      (f ⁻¹ᵁ (U i ⊓ U j)) (f.preimage_mono inf_le_left)
      (f.preimage_mono inf_le_right) =
    LineFrameTransitions318.scalar N (fun i => f ⁻¹ᵁ U i) en i j
      (f ⁻¹ᵁ (U i ⊓ U j)) (f.preimage_mono inf_le_left)
      (f.preimage_mono inf_le_right) at hij
  simpa only [Scheme.Hom.preimage_inf] using hij

/-- Tensor transitions multiply on complete inverse images of target opens. -/
lemma inverse_image_product (M N : X.Modules)
    (em : ∀ i, SheafOfModules.unit (f ⁻¹ᵁ U i).toScheme.ringCatSheaf ≅
      M.restrict (f ⁻¹ᵁ U i).ι)
    (en : ∀ i, SheafOfModules.unit (f ⁻¹ᵁ U i).toScheme.ringCatSheaf ≅
      N.restrict (f ⁻¹ᵁ U i).ι) :
    InverseImageLineCocycle318.cocycle f (IntrinsicTensorSheaf318.tensor M N) U
      (TensorLineCocycle318.frames M N (fun i => f ⁻¹ᵁ U i) em en) =
    UnitCocycleProduct318.product
      (InverseImageLineCocycle318.cocycle f M U em)
      (InverseImageLineCocycle318.cocycle f N U en) := by
  apply UnitTransitionCocycle318.Cocycle.ext
  intro i j
  exact TensorLineCocycle318.scalar_product M N (fun i => f ⁻¹ᵁ U i) em en
    i j (f ⁻¹ᵁ (U i ⊓ U j)) (f.preimage_mono inf_le_left)
    (f.preimage_mono inf_le_right)

variable (M N : Y.Modules)
    (em : ∀ i, SheafOfModules.unit (U i).toScheme.ringCatSheaf ≅ M.restrict (U i).ι)
    (en : ∀ i, SheafOfModules.unit (U i).toScheme.ringCatSheaf ≅ N.restrict (U i).ι)

/-- The unchanged pullback of the unchanged tensor sheaf has the same actual
source transitions as the tensor of the two unchanged pullback sheaves. -/
lemma comparison_cocycle :
    InverseImageLineCocycle318.cocycle f
      ((Scheme.Modules.pullback f).obj (IntrinsicTensorSheaf318.tensor M N)) U
      (fun i => LinePullbackFrames318.frame f (IntrinsicTensorSheaf318.tensor M N)
        (U i) (TensorLineCocycle318.frames M N U em en i)) =
    InverseImageLineCocycle318.cocycle f
      (IntrinsicTensorSheaf318.tensor ((Scheme.Modules.pullback f).obj M)
        ((Scheme.Modules.pullback f).obj N)) U
      (TensorLineCocycle318.frames ((Scheme.Modules.pullback f).obj M)
        ((Scheme.Modules.pullback f).obj N) (fun i => f ⁻¹ᵁ U i)
        (fun i => LinePullbackFrames318.frame f M (U i) (em i))
        (fun i => LinePullbackFrames318.frame f N (U i) (en i))) := by
  rw [LinePullbackTransitions318.cocycle, TensorLineCocycle318.cocycle_eq,
    UnitCocycleProduct318.map_product, inverse_image_product,
    LinePullbackTransitions318.cocycle, LinePullbackTransitions318.cocycle]

/-- A genuine isomorphism of the original module sheaves, reconstructed from
their exact pulled and tensor frames. Arbitrary scheme maps are allowed. -/
@[expose] def comparison (hc : (⊤ : Y.Opens) ≤ ⨆ i, U i) :
    (Scheme.Modules.pullback f).obj (IntrinsicTensorSheaf318.tensor M N) ≅
      IntrinsicTensorSheaf318.tensor ((Scheme.Modules.pullback f).obj M)
        ((Scheme.Modules.pullback f).obj N) :=
  FramedLineCocycleIso318.iso _ _ (fun i => f ⁻¹ᵁ U i)
    (fun i => LinePullbackFrames318.frame f (IntrinsicTensorSheaf318.tensor M N)
      (U i) (TensorLineCocycle318.frames M N U em en i))
    (TensorLineCocycle318.frames ((Scheme.Modules.pullback f).obj M)
      ((Scheme.Modules.pullback f).obj N) (fun i => f ⁻¹ᵁ U i)
      (fun i => LinePullbackFrames318.frame f M (U i) (em i))
      (fun i => LinePullbackFrames318.frame f N (U i) (en i)))
    (LinePullbackFrames318.preimage_cover f U hc)
    (source_cocycle_eq f U _ _ _ _ (comparison_cocycle f U M N em en))

lemma comparison_hom_inv (hc : (⊤ : Y.Opens) ≤ ⨆ i, U i) :
    (comparison f U M N em en hc).hom ≫ (comparison f U M N em en hc).inv = 𝟙 _ :=
  (comparison f U M N em en hc).hom_inv_id

lemma comparison_inv_hom (hc : (⊤ : Y.Opens) ≤ ⨆ i, U i) :
    (comparison f U M N em en hc).inv ≫ (comparison f U M N em en hc).hom = 𝟙 _ :=
  (comparison f U M N em en hc).inv_hom_id
end TensorPullbackCocycle318
