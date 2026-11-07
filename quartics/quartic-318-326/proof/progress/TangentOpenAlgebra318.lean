module
public import RelativeChordAlgebra318
public section
noncomputable section
namespace TangentOpenAlgebra318
open ShortAffineJacobian318 AffineEquationFunctor318
open RelativeChordAlgebra318 (PairRing leftPair rightPair)
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable {R:Type u} [CommRing R]

@[expose] def ordinateSum (A B:R) : PairRing A B := leftPair A B (y A B)+rightPair A B (y A B)
abbrev TangentRing (A B:R) := Localization.Away (ordinateSum A B)
@[expose] def left (A B:R) : Ring A B →ₐ[R] TangentRing A B :=
  (IsScalarTower.toAlgHom R (PairRing A B) (TangentRing A B)).comp (leftPair A B)
@[expose] def right (A B:R) : Ring A B →ₐ[R] TangentRing A B :=
  (IsScalarTower.toAlgHom R (PairRing A B) (TangentRing A B)).comp (rightPair A B)
@[expose] def x1 (A B:R) : TangentRing A B := left A B (x A B)
@[expose] def y1 (A B:R) : TangentRing A B := left A B (y A B)
@[expose] def x2 (A B:R) : TangentRing A B := right A B (x A B)
@[expose] def y2 (A B:R) : TangentRing A B := right A B (y A B)

theorem sum_unit (A B:R) : IsUnit (y1 A B+y2 A B) := by
  convert IsLocalization.Away.algebraMap_isUnit (S:=TangentRing A B) (ordinateSum A B) using 1
  simp only [ordinateSum,map_add,y1,y2,left,right,AlgHom.comp_apply]
  rfl
@[expose] def sumUnit (A B:R) : (TangentRing A B)ˣ := (sum_unit A B).unit
@[expose] def slope (A B:R) : TangentRing A B :=
  (x1 A B^2+x1 A B*x2 A B+x2 A B^2+algebraMap R (TangentRing A B) A)*↑(sumUnit A B)⁻¹
@[expose] def x3 (A B:R) : TangentRing A B := slope A B^2-x1 A B-x2 A B
@[expose] def y3 (A B:R) : TangentRing A B := slope A B*(x1 A B-x3 A B)-y1 A B

theorem slope_sum (A B:R) : slope A B*(y1 A B+y2 A B)=
    x1 A B^2+x1 A B*x2 A B+x2 A B^2+algebraMap R (TangentRing A B) A := by
  rw [slope,mul_assoc,←(sum_unit A B).unit_spec]
  change (x1 A B^2+x1 A B*x2 A B+x2 A B^2+algebraMap R (TangentRing A B) A)*
    (↑(sumUnit A B)⁻¹*↑(sumUnit A B))=_
  rw [Units.inv_mul,mul_one]

theorem first_equation (A B:R) :
    y1 A B^2-x1 A B^3-algebraMap R (TangentRing A B) A*x1 A B-
      algebraMap R (TangentRing A B) B=0 := by
  have hh:=congrArg (left A B) (relation A B)
  simpa only [map_sub,map_pow,map_mul,map_zero,AlgHom.commutes,x1,y1] using hh
theorem second_equation (A B:R) :
    y2 A B^2-x2 A B^3-algebraMap R (TangentRing A B) A*x2 A B-
      algebraMap R (TangentRing A B) B=0 := by
  have hh:=congrArg (right A B) (relation A B)
  simpa only [map_sub,map_pow,map_mul,map_zero,AlgHom.commutes,x2,y2] using hh

/-- The secant slope identity is derived without cancelling the abscissa difference. -/
theorem slope_gap (A B:R) : slope A B*(x2 A B-x1 A B)=y2 A B-y1 A B := by
  have hh : (y1 A B+y2 A B)*(slope A B*(x2 A B-x1 A B)-(y2 A B-y1 A B))=0 := by
    calc
      _ = (x2 A B-x1 A B)*(slope A B*(y1 A B+y2 A B)-
        (x1 A B^2+x1 A B*x2 A B+x2 A B^2+algebraMap R (TangentRing A B) A))+
        (y1 A B^2-x1 A B^3-algebraMap R (TangentRing A B) A*x1 A B-algebraMap R (TangentRing A B) B)-
        (y2 A B^2-x2 A B^3-algebraMap R (TangentRing A B) A*x2 A B-algebraMap R (TangentRing A B) B) := by ring
      _ = 0 := by rw [slope_sum,first_equation,second_equation]; ring
  exact sub_eq_zero.mp ((sum_unit A B).mul_left_cancel (hh.trans (mul_zero _).symm))

/-- Universal output identity valid even when the two abscissae coincide. -/
theorem tangent_identity (a b X1 Y1 X2 Y2 L:R) :
    let X3:=L^2-X1-X2
    let Y3:=L*(X1-X3)-Y1
    Y3^2-X3^3-a*X3-b = (Y1^2-X1^3-a*X1-b)+
      (X3-X1)*(L*(Y1+Y2)-(X1^2+X1*X2+X2^2+a)+L*(L*(X2-X1)-(Y2-Y1))) := by
  dsimp
  ring

theorem third_equation (A B:R) :
    y3 A B^2-x3 A B^3-algebraMap R (TangentRing A B) A*x3 A B-
      algebraMap R (TangentRing A B) B=0 := by
  have hh:=tangent_identity (algebraMap R (TangentRing A B) A)
    (algebraMap R (TangentRing A B) B) (x1 A B) (y1 A B) (x2 A B) (y2 A B) (slope A B)
  change (y3 A B^2-x3 A B^3-algebraMap R (TangentRing A B) A*x3 A B-
      algebraMap R (TangentRing A B) B)=_ at hh
  rw [first_equation,slope_sum,slope_gap] at hh
  simpa only [sub_self,mul_zero,add_zero,zero_add] using hh

@[expose] def tangentMap (A B:R) : Ring A B →ₐ[R] TangentRing A B :=
  toHom A B ⟨(x3 A B,y3 A B),third_equation A B⟩
@[simp] theorem tangentMap_x (A B:R) : tangentMap A B (x A B)=x3 A B := toHom_x _ _ _
@[simp] theorem tangentMap_y (A B:R) : tangentMap A B (y A B)=y3 A B := toHom_y _ _ _

end TangentOpenAlgebra318
