module
public import OriginalTensorPullbackAllCoverNaturality318
public section
noncomputable section
namespace OriginalLineTensorIsoNaturality318
open AlgebraicGeometry CategoryTheory LineSheafClass318
universe u
variable {X Y : Scheme.{u}} (p : X ⟶ Y) (L N L' N' : Line Y)
/-- Full naturality of the EXACT pre-existing tensorIso, with arbitrary
independent original line presentations. No alternate monoidal comparison
is introduced; both old literal common-refinement covers are consumed. -/
lemma natural (a : L.object ≅ L'.object) (b : N.object ≅ N'.object) :
    (Scheme.Modules.pullback p).mapIso (TensorSheafFunctor318.congr a b) ≪≫
      LineClassPullbackHom318.tensorIso p L' N'=
    LineClassPullbackHom318.tensorIso p L N ≪≫
      TensorSheafFunctor318.congr ((Scheme.Modules.pullback p).mapIso a)
        ((Scheme.Modules.pullback p).mapIso b) :=
  OriginalTensorPullbackAllCoverNaturality318.natural p
    (fun q : L.Index × N.Index => L.opens q.1 ⊓ N.opens q.2)
    (fun q : L'.Index × N'.Index => L'.opens q.1 ⊓ N'.opens q.2) a b
    (fun q => OpenLineFrameRefinement318.frame L.object (L.opens q.1) (L.frame q.1)
      (L.opens q.1 ⊓ N.opens q.2) inf_le_left)
    (fun q => OpenLineFrameRefinement318.frame N.object (N.opens q.2) (N.frame q.2)
      (L.opens q.1 ⊓ N.opens q.2) inf_le_right)
    (fun q => OpenLineFrameRefinement318.frame L'.object (L'.opens q.1) (L'.frame q.1)
      (L'.opens q.1 ⊓ N'.opens q.2) inf_le_left)
    (fun q => OpenLineFrameRefinement318.frame N'.object (N'.opens q.2) (N'.frame q.2)
      (L'.opens q.1 ⊓ N'.opens q.2) inf_le_right)
    (UnitCocycleRefinement318.common_cover L.opens N.opens L.cover N.cover)
    (UnitCocycleRefinement318.common_cover L'.opens N'.opens L'.cover N'.cover)
end OriginalLineTensorIsoNaturality318
