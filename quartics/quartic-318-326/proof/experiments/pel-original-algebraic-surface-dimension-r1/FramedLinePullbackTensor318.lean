module
public import InverseImageLineCocycleIso318
public import LinePullbackTransitions318
public import TensorInverseImageCocycle318
public section
noncomputable section
namespace FramedLinePullbackTensor318
open AlgebraicGeometry CategoryTheory IntrinsicTensorSheaf318
universe u
variable {X Y : Scheme.{u}} (f : X ⟶ Y) (M N : Y.Modules)
  {ι : Type u} (U : ι → Y.Opens)
  (em : ∀ i, SheafOfModules.unit (U i).toScheme.ringCatSheaf ≅ M.restrict (U i).ι)
  (en : ∀ i, SheafOfModules.unit (U i).toScheme.ringCatSheaf ≅ N.restrict (U i).ι)
abbrev pullFramesM := fun i => LinePullbackFrames318.frame f M (U i) (em i)
abbrev pullFramesN := fun i => LinePullbackFrames318.frame f N (U i) (en i)
abbrev leftFrames := fun i => LinePullbackFrames318.frame f (tensor M N) (U i)
  (TensorLineCocycle318.frames M N U em en i)
abbrev rightFrames := TensorLineCocycle318.frames
  ((Scheme.Modules.pullback f).obj M) ((Scheme.Modules.pullback f).obj N)
  (fun i => f ⁻¹ᵁ U i) (pullFramesM f M U em) (pullFramesN f N U en)

lemma cocycle :
    InverseImageLineCocycle318.cocycle f ((Scheme.Modules.pullback f).obj (tensor M N))
      U (leftFrames f M N U em en) =
    InverseImageLineCocycle318.cocycle f
      (tensor ((Scheme.Modules.pullback f).obj M) ((Scheme.Modules.pullback f).obj N))
      U (rightFrames f M N U em en) := by
  rw [LinePullbackTransitions318.cocycle, TensorLineCocycle318.cocycle_eq,
    UnitCocycleProduct318.map_product, TensorInverseImageCocycle318.cocycle_eq,
    LinePullbackTransitions318.cocycle, LinePullbackTransitions318.cocycle]

/-- Genuine tensor compatibility of the actual module-sheaf pullback.
It is reconstructed from full inverse-image frames, not assigned on classes. -/
@[expose] def iso (hc : (⊤ : Y.Opens) ≤ ⨆ i, U i) :
    (Scheme.Modules.pullback f).obj (tensor M N) ≅
      tensor ((Scheme.Modules.pullback f).obj M) ((Scheme.Modules.pullback f).obj N) :=
  InverseImageLineCocycleIso318.iso f _ _ U (leftFrames f M N U em en)
    (rightFrames f M N U em en) (cocycle f M N U em en) hc
end FramedLinePullbackTensor318
