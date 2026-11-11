module
public import InfinitesimalUnitCocycle318
public import PointedLineDeformation318
public import TensorPullbackCocycle318
public import StructureLineCocycleIso318
public section
noncomputable section
namespace UnitCocyclePointedLine318
open AlgebraicGeometry CategoryTheory Opposite PointedLineDeformation318
universe u
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {X₀ X : Scheme.{u}} (i : X₀ ⟶ X) {ι : Type u} (U : ι → X.Opens)
    (c : UnitTransitionCocycle318.Cocycle (StructureUnitsSheaf318.units X).obj U)
    (hc : (⊤ : X.Opens) ≤ ⨆ a, U a)
/-- Genuine unit-cocycle line with its unchanged coefficient-sheaf object. -/
@[expose] def line : LineSheafClass318.Line X where
  object := CocycleModule318.object U c
  Index := ι
  opens := U
  cover := hc
  frame := CocycleCanonicalTransitions318.frames U c
/-- Every original full-overlap transition reduces to one. -/
abbrev ReducesToOne := ∀ a b,
  Units.map (i.app (U a ⊓ U b)).hom.toMonoidHom (c.transition a b) = 1
include hc in
lemma pulled_cocycle_one (hr : ReducesToOne i U c) :
    InverseImageLineCocycle318.cocycle i ((Scheme.Modules.pullback i).obj (line U c hc).object) U
      (fun a => LinePullbackFrames318.frame i (line U c hc).object (U a) ((line U c hc).frame a)) =
    InverseImageLineCocycle318.cocycle i (SheafOfModules.unit X₀.ringCatSheaf) U
      (fun a => StructureLineFrames318.frame X₀ (i ⁻¹ᵁ U a)) := by
  rw [LinePullbackTransitions318.cocycle]
  change UnitTransitionCocycle318.map _
    (LineFrameCocycle318.cocycle (CocycleModule318.object U c) U
      (CocycleCanonicalTransitions318.frames U c)) = _
  rw [CocycleCanonicalTransitions318.cocycle_eq]
  apply UnitTransitionCocycle318.Cocycle.ext
  intro a b
  change Units.map (i.app (U a ⊓ U b)).hom.toMonoidHom (c.transition a b) = _
  rw [hr a b]
  exact (StructureLineFrames318.inverseImage_transition_one X₀ i U a b).symm
/-- The special-fiber frame is constructed from the actual pullback's canonical
frames and their proved original transitions, not assumed from a class label. -/
@[expose] def trivialization (hr : ReducesToOne i U c) :
    (Scheme.Modules.pullback i).obj (line U c hc).object ≅
      SheafOfModules.unit X₀.ringCatSheaf :=
  FramedLineCocycleIso318.iso _ _ (fun a => i ⁻¹ᵁ U a)
    (fun a => LinePullbackFrames318.frame i (line U c hc).object (U a) ((line U c hc).frame a))
    (fun a => StructureLineFrames318.frame X₀ (i ⁻¹ᵁ U a))
    (LinePullbackFrames318.preimage_cover i U hc)
    (TensorPullbackCocycle318.source_cocycle_eq i U _ _ _ _ (pulled_cocycle_one i U c hc hr))
@[expose] def deformation (hr : ReducesToOne i U c) : Deformation i where
  line := line U c hc
  trivialization := trivialization i U c hc hr
/-- The constructed frame preserves each original special-fiber coordinate map. -/
lemma trivialization_coordinate (hr : ReducesToOne i U c) (a : ι) :
    (trivialization i U c hc hr).hom ≫
      LineFrameAdjunction318.coordinate (SheafOfModules.unit X₀.ringCatSheaf) (i ⁻¹ᵁ U a)
        (StructureLineFrames318.frame X₀ (i ⁻¹ᵁ U a)) =
    LineFrameAdjunction318.coordinate ((Scheme.Modules.pullback i).obj (line U c hc).object)
      (i ⁻¹ᵁ U a)
      (LinePullbackFrames318.frame i (line U c hc).object (U a) ((line U c hc).frame a)) :=
  FramedLineCocycleIso318.coordinate _ _ _ _ _ _ _ a
/-- First-order transitions yield pointed actual lines whenever the actual
reduction map kills the specified epsilon on every full original open. -/
@[expose] def infinitesimal (e : Γ(X,⊤)) (he : e * e = 0)
    (c : InfinitesimalUnitCocycle318.AdditiveCocycle X U)
    (hz : ∀ V : X.Opens, i.app V (InfinitesimalUnitCocycle318.epsilon X e V) = 0) : Deformation i :=
  deformation i U (InfinitesimalUnitCocycle318.cocycle X e he U c) hc (by
    intro a b
    apply Units.ext
    change i.app _ (1 + InfinitesimalUnitCocycle318.epsilon X e _ * c.transition a b) = 1
    rw [map_add, map_one, map_mul, hz, zero_mul, add_zero])
end UnitCocyclePointedLine318
