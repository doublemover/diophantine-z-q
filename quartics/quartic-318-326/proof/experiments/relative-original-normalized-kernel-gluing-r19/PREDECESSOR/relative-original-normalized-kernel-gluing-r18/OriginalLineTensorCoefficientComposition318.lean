module
public import OriginalLineTensorIsoPresentation318
public section
noncomputable section
namespace OriginalLineTensorCoefficientComposition318
open AlgebraicGeometry CategoryTheory LineSheafClass318
universe u
variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (L N : Line Z)
/-- Coefficient composition for the exact native tensorIso used by the
old difference-frame map, with original pullback Line objects retained. -/
lemma composition :
    (Scheme.Modules.pullback f).mapIso (LineClassPullbackHom318.tensorIso g L N) ≪≫
      LineClassPullbackHom318.tensorIso f (LineSheafPullback318.line g L)
        (LineSheafPullback318.line g N) ≪≫
      TensorSheafFunctor318.congr ((Scheme.Modules.pullbackComp f g).app L.object)
        ((Scheme.Modules.pullbackComp f g).app N.object)=
    (Scheme.Modules.pullbackComp f g).app (LineSheafTensor318.line L N).object ≪≫
      LineClassPullbackHom318.tensorIso (f ≫ g) L N := by
  let U := fun q : L.Index × N.Index => L.opens q.1 ⊓ N.opens q.2
  let em := fun q : L.Index × N.Index => OpenLineFrameRefinement318.frame
    L.object (L.opens q.1) (L.frame q.1) (U q) inf_le_left
  let en := fun q : L.Index × N.Index => OpenLineFrameRefinement318.frame
    N.object (N.opens q.2) (N.frame q.2) (U q) inf_le_right
  have hc : (⊤:Z.Opens)≤⨆q,U q :=
    UnitCocycleRefinement318.common_cover L.opens N.opens L.cover N.cover
  have h := OriginalTensorComparisonCoefficientComposition318.composition f g U L.object N.object em en hc
  rw [OriginalLineTensorIsoPresentation318.comparison g L N,
    OriginalLineTensorIsoPresentation318.comparison f (LineSheafPullback318.line g L)
      (LineSheafPullback318.line g N),
    OriginalLineTensorIsoPresentation318.comparison (f ≫ g) L N] at h
  exact h
end OriginalLineTensorCoefficientComposition318
