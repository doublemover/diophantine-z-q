module
public import LineClassInverse318
public import LineSheafTensorIsos318
public section
noncomputable section
namespace LineSheafClassGroup318
open AlgebraicGeometry CategoryTheory LineSheafClass318
universe u
variable {X : Scheme.{u}}
lemma product_assoc (a b c : Class X) :
    LineSheafTensor318.product (LineSheafTensor318.product a b) c =
      LineSheafTensor318.product a (LineSheafTensor318.product b c) :=
  Quotient.inductionOn₃ a b c (fun L N P => classOf_eq (LineSheafTensorIsos318.assoc L N P))
lemma product_comm (a b : Class X) :
    LineSheafTensor318.product a b = LineSheafTensor318.product b a :=
  Quotient.inductionOn₂ a b (fun L N => classOf_eq (LineSheafTensorIsos318.comm L N))
lemma unit_product (a : Class X) :
    LineSheafTensor318.product (LineSheafUnit318.unitClass X) a = a :=
  Quotient.inductionOn a (fun L => classOf_eq (LineSheafTensorIsos318.leftUnit L))
lemma product_unit (a : Class X) :
    LineSheafTensor318.product a (LineSheafUnit318.unitClass X) = a :=
  Quotient.inductionOn a (fun L => classOf_eq (LineSheafTensorIsos318.rightUnit L))
/-- The group of isomorphism classes of genuine original locally framed line
sheaves. All operations are induced by the actual tensor, structure sheaf
and inverse-line cancellation. This does not assert representability. -/
@[expose] instance classCommGroup (X : Scheme.{u}) : CommGroup (Class X) where
  mul := LineSheafTensor318.product
  one := LineSheafUnit318.unitClass X
  inv := LineClassInverse318.inverse
  mul_assoc := product_assoc
  mul_comm := product_comm
  one_mul := unit_product
  mul_one := product_unit
  inv_mul_cancel := LineClassInverse318.inverse_product
lemma classOf_tensor (L N : Line X) :
    classOf (LineSheafTensor318.line L N) = classOf L * classOf N := rfl
lemma classOf_structure : classOf (LineSheafUnit318.line X) = (1 : Class X) := rfl
lemma classOf_inverse (L : Line X) :
    classOf (FramedLineInverse318.inverse L) = (classOf L)⁻¹ := by
  apply mul_left_cancel (a := classOf L)
  calc
    classOf L * classOf (FramedLineInverse318.inverse L) = 1 :=
      classOf_eq (FramedLineInverse318.rightIso L)
    _ = classOf L * (classOf L)⁻¹ := (mul_inv_cancel _).symm
end LineSheafClassGroup318
