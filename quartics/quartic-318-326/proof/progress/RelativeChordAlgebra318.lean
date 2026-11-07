module
public import AffineSchemeSolutions318
public import Mathlib.RingTheory.Localization.Away.Basic
public section
noncomputable section
namespace RelativeChordAlgebra318
open ShortAffineJacobian318 AffineEquationFunctor318
open scoped TensorProduct
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency.types false
variable {R:Type u} [CommRing R]

abbrev PairRing (A B:R) := Ring A B ⊗[R] Ring A B
@[expose] def leftPair (A B:R) : Ring A B →ₐ[R] PairRing A B := Algebra.TensorProduct.includeLeft
@[expose] def rightPair (A B:R) : Ring A B →ₐ[R] PairRing A B := Algebra.TensorProduct.includeRight
@[expose] def gap (A B:R) : PairRing A B := rightPair A B (x A B)-leftPair A B (x A B)
abbrev ChordRing (A B:R) := Localization.Away (gap A B)
@[expose] def left (A B:R) : Ring A B →ₐ[R] ChordRing A B :=
  (IsScalarTower.toAlgHom R (PairRing A B) (ChordRing A B)).comp (leftPair A B)
@[expose] def right (A B:R) : Ring A B →ₐ[R] ChordRing A B :=
  (IsScalarTower.toAlgHom R (PairRing A B) (ChordRing A B)).comp (rightPair A B)
@[expose] def x1 (A B:R) : ChordRing A B := left A B (x A B)
@[expose] def y1 (A B:R) : ChordRing A B := left A B (y A B)
@[expose] def x2 (A B:R) : ChordRing A B := right A B (x A B)
@[expose] def y2 (A B:R) : ChordRing A B := right A B (y A B)

theorem gap_unit (A B:R) : IsUnit (x2 A B-x1 A B) := by
  convert IsLocalization.Away.algebraMap_isUnit (S:=ChordRing A B) (gap A B) using 1
  simp only [gap,map_sub,x1,x2,left,right,AlgHom.comp_apply]
  rfl

@[expose] def gapUnit (A B:R) : (ChordRing A B)ˣ := (gap_unit A B).unit
@[expose] def slope (A B:R) : ChordRing A B := (y2 A B-y1 A B)*↑(gapUnit A B)⁻¹
@[expose] def x3 (A B:R) : ChordRing A B := slope A B^2-x1 A B-x2 A B
@[expose] def y3 (A B:R) : ChordRing A B := slope A B*(x1 A B-x3 A B)-y1 A B

theorem slope_identity (A B:R) : slope A B*(x2 A B-x1 A B)=y2 A B-y1 A B := by
  rw [slope,mul_assoc,←(gap_unit A B).unit_spec]
  change (y2 A B-y1 A B)*(↑(gapUnit A B)⁻¹*↑(gapUnit A B))=_
  rw [Units.inv_mul,mul_one]

theorem first_equation (A B:R) :
    y1 A B^2-x1 A B^3-algebraMap R (ChordRing A B) A*x1 A B-
      algebraMap R (ChordRing A B) B=0 := by
  have hh:=congrArg (left A B) (relation A B)
  simpa only [map_sub,map_pow,map_mul,map_zero,AlgHom.commutes,x1,y1,x2,y2] using hh

theorem second_equation (A B:R) :
    y2 A B^2-x2 A B^3-algebraMap R (ChordRing A B) A*x2 A B-
      algebraMap R (ChordRing A B) B=0 := by
  have hh:=congrArg (right A B) (relation A B)
  simpa only [map_sub,map_pow,map_mul,map_zero,AlgHom.commutes,x1,y1,x2,y2] using hh

/-- Universal ordinary-chord identity over any commutative ring. -/
theorem chord_identity (a b X1 Y1 X2 Y2 L:R) :
    let X3:=L^2-X1-X2
    let Y3:=L*(X1-X3)-Y1
    (X2-X1)*(Y3^2-X3^3-a*X3-b)=
      (X2-X3)*(Y1^2-X1^3-a*X1-b)+
      (X3-X1)*(Y2^2-X2^3-a*X2-b)+
      (X3-X1)*(Y1+L*(X2-X1)+Y2)*(L*(X2-X1)-(Y2-Y1)) := by
  dsimp
  ring

/-- The actual output satisfies the equation inside the localized tensor algebra. -/
theorem third_equation (A B:R) :
    y3 A B^2-x3 A B^3-algebraMap R (ChordRing A B) A*x3 A B-
      algebraMap R (ChordRing A B) B=0 := by
  have hh:=chord_identity (algebraMap R (ChordRing A B) A)
    (algebraMap R (ChordRing A B) B) (x1 A B) (y1 A B) (x2 A B) (y2 A B) (slope A B)
  change (x2 A B-x1 A B)*(y3 A B^2-x3 A B^3-algebraMap R (ChordRing A B) A*x3 A B-
      algebraMap R (ChordRing A B) B)=_ at hh
  rw [first_equation,second_equation,slope_identity,sub_self] at hh
  simp only [mul_zero,add_zero] at hh
  exact (gap_unit A B).mul_left_cancel (hh.trans (mul_zero _).symm)

/-- Actual coordinate algebra map defining the relative ordinary-chord morphism. -/
@[expose] def chordMap (A B:R) : Ring A B →ₐ[R] ChordRing A B :=
  toHom A B ⟨(x3 A B,y3 A B),third_equation A B⟩
@[simp] theorem chordMap_x (A B:R) : chordMap A B (x A B)=x3 A B := toHom_x _ _ _
@[simp] theorem chordMap_y (A B:R) : chordMap A B (y A B)=y3 A B := toHom_y _ _ _

end RelativeChordAlgebra318
