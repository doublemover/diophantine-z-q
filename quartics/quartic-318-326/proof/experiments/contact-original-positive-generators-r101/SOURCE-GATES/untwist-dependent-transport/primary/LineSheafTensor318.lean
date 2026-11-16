module
public import LineSheafClass318
public import TensorLineLocalFrame318
public import OpenLineFrameRefinement318
public section
noncomputable section
namespace LineSheafTensor318
open AlgebraicGeometry CategoryTheory LineSheafClass318
set_option maxHeartbeats 450000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X : Scheme.{u}}
/-- The actual tensor sheaf, framed on the genuine common refinement of the
original two covering families. -/
@[expose] def line (L N : Line X) : Line X where
  object := IntrinsicTensorSheaf318.tensor L.object N.object
  Index := L.Index × N.Index
  opens := fun p => L.opens p.1 ⊓ N.opens p.2
  cover := UnitCocycleRefinement318.common_cover L.opens N.opens L.cover N.cover
  frame := fun p => TensorLineLocalFrame318.frame L.object N.object _
    (OpenLineFrameRefinement318.frame L.object (L.opens p.1) (L.frame p.1) _ inf_le_left)
    (OpenLineFrameRefinement318.frame N.object (N.opens p.2) (N.frame p.2) _ inf_le_right)
/-- Actual tensor functoriality, not an assigned relation on cocycle labels. -/
def congr {L L' N N' : Line X} (e : L.object ≅ L'.object) (f : N.object ≅ N'.object) :
    (line L N).object ≅ (line L' N').object := TensorSheafFunctor318.congr e f
lemma respects {L L' N N' : Line X} (h : Related L L') (k : Related N N') :
    Related (line L N) (line L' N') := by
  obtain ⟨e⟩ := h
  obtain ⟨f⟩ := k
  exact ⟨congr e f⟩
/-- The genuine tensor product descends to original sheaf isomorphism classes.
Associativity, unit laws and inverses are separate statements. -/
@[expose] def product : Class X → Class X → Class X :=
  Quotient.map₂ line (fun _ _ h _ _ k => respects h k)
lemma product_classOf (L N : Line X) :
    product (classOf L) (classOf N) = classOf (line L N) := rfl
lemma presentation_independent {L L' N N' : Line X}
    (e : L.object ≅ L'.object) (f : N.object ≅ N'.object) :
    product (classOf L) (classOf N) = product (classOf L') (classOf N') :=
  classOf_eq (congr e f)
end LineSheafTensor318
