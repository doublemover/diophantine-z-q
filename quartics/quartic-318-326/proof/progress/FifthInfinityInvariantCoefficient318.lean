module
public import InfinityGlobalDifferentialRestriction318
public import QuadraticCoordinateDerivative318
public import FifthSourceInfinityAlgebra318
public import WeierstrassAffineInvariantEquation318
public section
noncomputable section
namespace FifthInfinityInvariantCoefficient318
open AlgebraicGeometry CategoryTheory Opposite SourceTwistArithmetic318
open FifthCharacterShortPolynomial318 FifthSourceInfinityCoordinates318
set_option maxHeartbeats 500000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
abbrev r:=InfinityOrderCoordinates318.coordinate units
@[expose] def numerator:I:=algebraMap ℚ I (2*(xScale:ℚ)*(↑((units 0)⁻¹):ℚ))
lemma numerator_unit:IsUnit numerator:=by
  exact ((IsUnit.mk0 (2:ℚ) (by norm_num)).mul xScale.isUnit |>.mul ((units 0)⁻¹).isUnit).map (algebraMap ℚ I)
lemma y_unit:IsUnit y:=by
  unfold y v
  apply IsUnit.mul ((yScale.isUnit).map (algebraMap ℚ I))
  apply IsUnit.mul (((units 0).isUnit.map (algebraMap ℚ I)).pow 2)
  exact IsUnit.prod_iff.mpr (fun i _=>InfinityCharacterUnits318.indexedRatio_unit units i)
lemma two_y_unit:IsUnit (2*y):=by
  simpa only [map_ofNat] using ((IsUnit.mk0 (2:ℚ) (by norm_num)).map (algebraMap ℚ I)).mul y_unit
@[expose] def inverseTwoY:I:=↑(two_y_unit.unit⁻¹)
lemma inverse_relation:inverseTwoY*(2*y)=1:=by
  rw [←two_y_unit.unit_spec]
  exact Units.inv_mul _
/-- Exact derivative numerator for X=m*(u^2/c0)+k on the entire chart. -/
theorem derivative_x:KaehlerDifferential.D ℚ I x=
    (numerator*r) • KaehlerDifferential.D ℚ I r:=by
  change KaehlerDifferential.D ℚ I
    (algebraMap ℚ I (xScale:ℚ)*(algebraMap ℚ I (↑((units 0)⁻¹):ℚ)*r^2)+algebraMap ℚ I shift)=_
  exact QuadraticCoordinateDerivative318.equation (xScale:ℚ) (↑((units 0)⁻¹):ℚ) shift r
@[expose] def pulled:KaehlerDifferential ℚ I:=AlgHomDifferential318.map
  FifthSourceInfinityAlgebra318.shortMap (WeierstrassAffineInvariant318.form A B discriminant_unit)
lemma invariant_equation:(2*y) • pulled=KaehlerDifferential.D ℚ I x:=by
  have h:=congrArg (AlgHomDifferential318.map FifthSourceInfinityAlgebra318.shortMap)
    (WeierstrassAffineInvariantEquation318.equation A B discriminant_unit)
  simpa only [AlgHomDifferential318.map_smul,AlgHomDifferential318.map_D,map_mul,map_ofNat,
    FifthSourceInfinityAlgebra318.shortMap_x,FifthSourceInfinityAlgebra318.shortMap_y,pulled] using h
/-- The exact whole-chart unit multiplying u du; all coordinate scales are
retained from the specified actual short-model map. -/
@[expose] def factor:I:=inverseTwoY*numerator
lemma factor_unit:IsUnit factor:=
  (Units.isUnit (two_y_unit.unit⁻¹)).mul numerator_unit
/-- Normalization uses the actual denominator-free invariant equation,
with a denominator proved a unit everywhere on the infinity chart. -/
theorem normalized:pulled=(factor*r) • KaehlerDifferential.D ℚ I r:=by
  have h:=QuadraticCoordinateDerivative318.isolate (K:=I) (V:=KaehlerDifferential ℚ I)
    (2*y) (numerator*r) inverseTwoY pulled (KaehlerDifferential.D ℚ I r)
    inverse_relation (invariant_equation.trans derivative_x)
  simpa only [factor,mul_assoc] using h
end FifthInfinityInvariantCoefficient318
