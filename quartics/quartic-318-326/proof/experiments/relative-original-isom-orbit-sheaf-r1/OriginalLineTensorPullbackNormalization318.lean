module
public import OriginalTensorPullbackNaturality318
public import LineClassPullbackHom318
public section
noncomputable section
namespace OriginalLineTensorPullbackNormalization318
open AlgebraicGeometry CategoryTheory LineSheafClass318
universe u
variable {X Y : Scheme.{u}} (p : X ⟶ Y) (L N : Line Y)
local notation "V" => fun q : L.Index × N.Index => L.opens q.1 ⊓ N.opens q.2
local notation "em" => fun q : L.Index × N.Index =>
  OpenLineFrameRefinement318.frame L.object (L.opens q.1) (L.frame q.1)
    (L.opens q.1 ⊓ N.opens q.2) inf_le_left
local notation "en" => fun q : L.Index × N.Index =>
  OpenLineFrameRefinement318.frame N.object (N.opens q.2) (N.frame q.2)
    (L.opens q.1 ⊓ N.opens q.2) inf_le_right
local notation "hc" => UnitCocycleRefinement318.common_cover L.opens N.opens L.cover N.cover
/-- Exact original tensorIso normalization on its literal common-refined
charts. This is the comparison used by the existing pulled difference map. -/
lemma frame (q : L.Index × N.Index) :
    LinePullbackFrames318.frame p (IntrinsicTensorSheaf318.tensor L.object N.object) (V q)
      (TensorLineCocycle318.frames L.object N.object V em en q) ≪≫
        (Scheme.Modules.restrictFunctor (p ⁻¹ᵁ V q).ι).mapIso
          (LineClassPullbackHom318.tensorIso p L N)=
    TensorLineCocycle318.frames ((Scheme.Modules.pullback p).obj L.object)
      ((Scheme.Modules.pullback p).obj N.object) (fun q => p ⁻¹ᵁ V q)
      (fun q => LinePullbackFrames318.frame p L.object (V q) (em q))
      (fun q => LinePullbackFrames318.frame p N.object (V q) (en q)) q :=
  OriginalTensorPullbackFrameNormalization318.frame p V L.object N.object em en hc q
/-- The existing native comparison participates in the proved naturality
square when the SAME refined frames are transported to the target modules.
No equality with a comparison from independently chosen target frames is
silently substituted here. -/
lemma transported_natural {M' N' : Y.Modules} (a : L.object ≅ M') (b : N.object ≅ N') :
    (Scheme.Modules.pullback p).mapIso (TensorSheafFunctor318.congr a b) ≪≫
      TensorPullbackCocycle318.comparison p V M' N'
        (fun q => em q ≪≫ (Scheme.Modules.restrictFunctor (V q).ι).mapIso a)
        (fun q => en q ≪≫ (Scheme.Modules.restrictFunctor (V q).ι).mapIso b) hc=
    LineClassPullbackHom318.tensorIso p L N ≪≫
      TensorSheafFunctor318.congr ((Scheme.Modules.pullback p).mapIso a)
        ((Scheme.Modules.pullback p).mapIso b) :=
  OriginalTensorPullbackNaturality318.natural p V a b em en hc
end OriginalLineTensorPullbackNormalization318
