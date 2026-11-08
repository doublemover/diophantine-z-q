module
public import FifthOverlapCoordinates318
public import WeierstrassAffineInvariantEquation318
public section
noncomputable section
namespace FifthOverlapDifferentialEquation318
open KaehlerDifferential SourceTwistArithmetic318 FifthCharacterShortPolynomial318
open FifthOverlapCoordinates318
set_option maxHeartbeats 450000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
attribute [-instance] DivisionRing.toRatAlgebra
@[expose] def delta (r:O):O:=ContactUnbranchedDifferentialFrame318.frame units (D ℚ O r)
lemma delta_mul (a b:O):delta (a*b)=a*delta b+b*delta a:=by
  simp only [delta,Derivation.leibniz,map_add,map_smul,smul_eq_mul]
lemma delta_add (a b:O):delta (a+b)=delta a+delta b:=by simp only [delta,map_add]
lemma delta_constant (a:ℚ):delta (algebraMap ℚ O a)=0:=by
  simp only [delta,Derivation.map_algebraMap,map_zero]
lemma delta_t:delta t=1:=by
  rw [delta,t_coordinate,ContactUnbranchedDifferentialFrame318.frame_D]
/-- Differentiate the exact denominator-cleared x relation on the entire
unbranched order, retaining the negative reciprocal-coordinate derivative. -/
theorem derivative_equation:delta x*t^2= -algebraMap ℚ O (xScale:ℚ):=by
  have hd:=congrArg delta x_relation
  rw [delta_mul,delta_add,delta_constant,delta_mul,delta_constant,delta_t] at hd
  simp only [mul_one,mul_zero,zero_add,add_zero] at hd
  have hx:=x_relation
  linear_combination t*hd-hx

@[expose] def pulled:KaehlerDifferential ℚ O:=
  AlgHomDifferential318.map FifthSourceOverlap318.shortMap
    (WeierstrassAffineInvariant318.form A B discriminant_unit)
@[expose] def coefficient:O:=ContactUnbranchedDifferentialFrame318.frame units pulled

theorem invariant_equation:(2*y)*coefficient=delta x:=by
  have h:=congrArg (AlgHomDifferential318.map FifthSourceOverlap318.shortMap)
    (WeierstrassAffineInvariantEquation318.equation A B discriminant_unit)
  rw [AlgHomDifferential318.map_smul,AlgHomDifferential318.map_D,map_mul,map_ofNat] at h
  have hf:=congrArg (ContactUnbranchedDifferentialFrame318.frame units) h
  simpa only [map_smul,smul_eq_mul,coefficient,pulled,delta,x,y] using hf

/-- The pulled invariant satisfies a denominator-free normalized equation
in the whole overlap ring. The only inverses used later are in the specified field. -/
theorem normalized_equation:(2*algebraMap ℚ O (yScale:ℚ)*w)*coefficient=
    -algebraMap ℚ O (xScale:ℚ):=by
  have h1:=invariant_equation
  have h2:=derivative_equation
  have h3:=y_relation
  linear_combination t^2*h1+h2-2*coefficient*h3
end FifthOverlapDifferentialEquation318
