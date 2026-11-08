module
public import LineSheafTensor318
public import LineSheafUnit318
public import FramedLineInverse318
public section
noncomputable section
namespace LineClassInverse318
open AlgebraicGeometry CategoryTheory LineSheafClass318
universe u
variable {X : Scheme.{u}}
/-- An inverse representative exists for every original class, with both
actual tensor-cancellation equalities. -/
lemma exists_inverse (c : Class X) : ∃ d : Class X,
    LineSheafTensor318.product c d = LineSheafUnit318.unitClass X ∧
    LineSheafTensor318.product d c = LineSheafUnit318.unitClass X := by
  induction c using LineSheafClass318.induction with
  | h L =>
    exact ⟨classOf (FramedLineInverse318.inverse L),
      classOf_eq (FramedLineInverse318.rightIso L),
      classOf_eq (FramedLineInverse318.leftIso L)⟩
/-- A chosen actual inverse class. Group laws are established separately,
not assumed in the choice or existence theorem. -/
@[expose] def inverse (c : Class X) : Class X := Classical.choose (exists_inverse c)
lemma product_inverse (c : Class X) :
    LineSheafTensor318.product c (inverse c) = LineSheafUnit318.unitClass X :=
  (Classical.choose_spec (exists_inverse c)).1
lemma inverse_product (c : Class X) :
    LineSheafTensor318.product (inverse c) c = LineSheafUnit318.unitClass X :=
  (Classical.choose_spec (exists_inverse c)).2
end LineClassInverse318
