module
public import HomogeneousAddition318
public import InfinityChart318
public section
noncomputable section
namespace InfinityAdditionAlgebra318
open ShortAffineJacobian318
open RelativeChordAlgebra318 (PairRing leftPair rightPair)
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable {R:Type u} [CommRing R]

@[expose] def coeffMap (A B:R) : R →ₐ[R] PairRing A B := Algebra.ofId R (PairRing A B)

/-- Two actual input coordinates before any localization. -/
@[expose] def X1 (A B:R) : PairRing A B := leftPair A B (x A B)
@[expose] def Y1 (A B:R) : PairRing A B := leftPair A B (y A B)
@[expose] def X2 (A B:R) : PairRing A B := rightPair A B (x A B)
@[expose] def Y2 (A B:R) : PairRing A B := rightPair A B (y A B)

theorem first_equation (A B:R) : Y1 A B^2-X1 A B^3-coeffMap A B A*X1 A B-
    coeffMap A B B=0 := by
  have h1 : leftPair A B 1=1 := (leftPair A B).toRingHom.map_one
  have hh:=congrArg (leftPair A B) (relation A B)
  simpa only [map_sub,pow_succ,pow_zero,mul_one,h1,map_mul,map_zero,AlgHom.commutes,X1,Y1,coeffMap,Algebra.ofId_apply] using hh
theorem second_equation (A B:R) : Y2 A B^2-X2 A B^3-coeffMap A B A*X2 A B-
    coeffMap A B B=0 := by
  have h1 : rightPair A B 1=1 := (rightPair A B).toRingHom.map_one
  have hh:=congrArg (rightPair A B) (relation A B)
  simpa only [map_sub,pow_succ,pow_zero,mul_one,h1,map_mul,map_zero,AlgHom.commutes,X2,Y2,coeffMap,Algebra.ofId_apply] using hh

/-- false selects chord data; true selects the complementary tangent/secant data. -/
@[expose] def denominator (A B:R) (tangent:Bool) : PairRing A B :=
  if tangent then Y1 A B+Y2 A B else X2 A B-X1 A B
@[expose] def slopeNumerator (A B:R) (tangent:Bool) : PairRing A B :=
  if tangent then X1 A B^2+X1 A B*X2 A B+X2 A B^2+coeffMap A B A
    else Y2 A B-Y1 A B
@[expose] def numeratorX (A B:R) (tangent:Bool) : PairRing A B :=
  slopeNumerator A B tangent^2-(X1 A B+X2 A B)*denominator A B tangent^2
@[expose] def numeratorY (A B:R) (tangent:Bool) : PairRing A B :=
  slopeNumerator A B tangent*(X1 A B*denominator A B tangent^2-numeratorX A B tangent)-
    Y1 A B*denominator A B tangent^3

/-- The actual homogeneous cubic identity in the genuine pair coordinate algebra. -/
theorem homogeneous_equation (A B:R) (tangent:Bool) :
    numeratorY A B tangent^2-numeratorX A B tangent^3-
      coeffMap A B A*numeratorX A B tangent*denominator A B tangent^4-
      coeffMap A B B*denominator A B tangent^6=0 := by
  cases tangent
  · simpa only [numeratorX,numeratorY,denominator,slopeNumerator,Bool.false_eq_true,ite_false]
      using HomogeneousAddition318.chord_numerator (R:=PairRing A B) (coeffMap A B A) (coeffMap A B B)
        (X1 A B) (Y1 A B) (X2 A B) (Y2 A B) (first_equation A B) (second_equation A B)
  · simpa only [numeratorX,numeratorY,denominator,slopeNumerator,ite_true]
      using HomogeneousAddition318.tangent_numerator (R:=PairRing A B) (coeffMap A B A) (coeffMap A B B)
        (X1 A B) (Y1 A B) (X2 A B) (Y2 A B) (first_equation A B) (second_equation A B)

/-- The actual output-infinity open, inverting the homogeneous Y numerator. -/
abbrev OutputRing (A B:R) (tangent:Bool) := Localization.Away (numeratorY A B tangent)
@[expose] def pairMap (A B:R) (tangent:Bool) : PairRing A B →ₐ[R] OutputRing A B tangent :=
  IsScalarTower.toAlgHom R (PairRing A B) (OutputRing A B tangent)

theorem numeratorY_unit (A B:R) (tangent:Bool) :
    IsUnit (pairMap A B tangent (numeratorY A B tangent)) :=
  IsLocalization.Away.algebraMap_isUnit (S:=OutputRing A B tangent) (numeratorY A B tangent)
@[expose] def numeratorYUnit (A B:R) (tangent:Bool) : (OutputRing A B tangent)ˣ :=
  (numeratorY_unit A B tangent).unit
@[expose] def outX (A B:R) (tangent:Bool) : OutputRing A B tangent :=
  pairMap A B tangent (numeratorX A B tangent)*pairMap A B tangent (denominator A B tangent)*
    ↑(numeratorYUnit A B tangent)⁻¹
@[expose] def outZ (A B:R) (tangent:Bool) : OutputRing A B tangent :=
  pairMap A B tangent (denominator A B tangent)^3*↑(numeratorYUnit A B tangent)⁻¹

/-- The exact Y=1 chart equation is derived from the actual homogeneous identity. -/
theorem output_equation (A B:R) (tangent:Bool) :
    outZ A B tangent-outX A B tangent^3-
      algebraMap R (OutputRing A B tangent) A*outX A B tangent*outZ A B tangent^2-
      algebraMap R (OutputRing A B tangent) B*outZ A B tangent^3=0 := by
  have hh:=congrArg (pairMap A B tangent) (homogeneous_equation A B tangent)
  have hm (a:PairRing A B) (n:ℕ) : pairMap A B tangent (a^n)=(pairMap A B tangent a)^n := by
    induction n with
    | zero =>
        simp only [pow_zero]
        change algebraMap (PairRing A B) (OutputRing A B tangent) 1=1
        exact (algebraMap (PairRing A B) (OutputRing A B tangent)).map_one
    | succ n ih => simp only [pow_succ,map_mul,ih]
  simp only [map_sub,hm,map_mul,map_zero,AlgHom.commutes,coeffMap,Algebra.ofId_apply] at hh
  apply HomogeneousAddition318.infinity_equation _ _ _ _ _ _ hh
  change pairMap A B tangent (numeratorY A B tangent)*↑(numeratorYUnit A B tangent)⁻¹=1
  rw [←(numeratorY_unit A B tangent).unit_spec]
  exact Units.mul_inv _

/-- Genuine quotient-algebra map into the whole actual infinity chart. -/
@[expose] def outputMap (A B:R) (tangent:Bool) :
    InfinityChart318.Ring A B →ₐ[R] OutputRing A B tangent :=
  InfinityChart318.lift A B (outX A B tangent) (outZ A B tangent) (output_equation A B tangent)
@[simp] theorem outputMap_x (A B:R) (tangent:Bool) :
    outputMap A B tangent (InfinityChart318.x A B)=outX A B tangent :=
  InfinityChart318.lift_x _ _ _ _ _
@[simp] theorem outputMap_z (A B:R) (tangent:Bool) :
    outputMap A B tangent (InfinityChart318.z A B)=outZ A B tangent :=
  InfinityChart318.lift_z _ _ _ _ _

end InfinityAdditionAlgebra318
