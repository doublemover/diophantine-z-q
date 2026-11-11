module
public import FramedLinePullbackTensor318
public import LineClassPullbackLaws318
public import LineSheafClassGroup318
public section
noncomputable section
namespace LineClassPullbackGroup318
open AlgebraicGeometry CategoryTheory LineSheafClass318
universe u
variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- Whole-sheaf tensor compatibility on the actual common refinement
of two independently presented lines. -/
@[expose] def tensorIso (L N : Line Y) :
    (LineSheafPullback318.line f (LineSheafTensor318.line L N)).object ≅
      (LineSheafTensor318.line (LineSheafPullback318.line f L)
        (LineSheafPullback318.line f N)).object :=
  FramedLinePullbackTensor318.iso f L.object N.object
    (fun p : L.Index × N.Index => L.opens p.1 ⊓ N.opens p.2)
    (fun p => OpenLineFrameRefinement318.frame L.object (L.opens p.1) (L.frame p.1)
      _ inf_le_left)
    (fun p => OpenLineFrameRefinement318.frame N.object (N.opens p.2) (N.frame p.2)
      _ inf_le_right)
    (UnitCocycleRefinement318.common_cover L.opens N.opens L.cover N.cover)

lemma map_mul (a b : Class Y) :
    LineSheafPullback318.pullback f (a*b) =
      LineSheafPullback318.pullback f a * LineSheafPullback318.pullback f b := by
  induction a using LineSheafClass318.induction with
  | h L =>
    induction b using LineSheafClass318.induction with
    | h N => exact classOf_eq (tensorIso f L N)
lemma map_one : LineSheafPullback318.pullback f (1 : Class Y) = 1 :=
  classOf_eq (IdentityCotangent318.pullbackUnitIso f)

/-- Pullback is a genuine homomorphism of whole line-sheaf isomorphism
classes, with multiplicativity proved by actual module-sheaf isomorphisms. -/
@[expose] def hom : Class Y →* Class X where
  toFun := LineSheafPullback318.pullback f
  map_one' := map_one f
  map_mul' := map_mul f

/-- Base change of an actual tensor difference, including inverse
lines, follows from the group law induced by full sheaf cancellation. -/
@[expose] def differenceIso (L N : Line Y) :
    (LineSheafPullback318.line f
      (LineSheafTensor318.line L (FramedLineInverse318.inverse N))).object ≅
    (LineSheafTensor318.line (LineSheafPullback318.line f L)
      (FramedLineInverse318.inverse (LineSheafPullback318.line f N))).object := by
  apply Classical.choice
  apply (classOf_eq_iff _ _).mp
  change hom f (classOf (LineSheafTensor318.line L (FramedLineInverse318.inverse N))) = _
  rw [LineSheafClassGroup318.classOf_tensor,LineSheafClassGroup318.classOf_inverse,
    (hom f).map_mul,(hom f).map_inv,LineSheafClassGroup318.classOf_tensor,
    LineSheafClassGroup318.classOf_inverse]
  rfl
end LineClassPullbackGroup318
