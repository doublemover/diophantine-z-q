module
public import InfinityInputPolynomial318
public import InfinityAdditionAlgebra318
public section
noncomputable section
namespace InfinityInputAlgebra318
open scoped TensorProduct
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable {R:Type u} [CommRing R]

lemma map_power {T S:Type u} [CommRing T] [CommRing S] [Algebra R T] [Algebra R S]
    (f:T →ₐ[R] S) (a:T) (n:ℕ) : f (a^n)=(f a)^n := by
  induction n with
  | zero =>
      simp only [pow_zero]
      exact f.toRingHom.map_one
  | succ n ih => simp only [pow_succ,map_mul,ih]

abbrev PairRing (A B:R) := InfinityChart318.Ring A B ⊗[R] ShortAffineJacobian318.Ring A B
@[expose] def left (A B:R) : InfinityChart318.Ring A B →ₐ[R] PairRing A B := Algebra.TensorProduct.includeLeft
@[expose] def right (A B:R) : ShortAffineJacobian318.Ring A B →ₐ[R] PairRing A B := Algebra.TensorProduct.includeRight
@[expose] def coeff (A B:R) : R →ₐ[R] PairRing A B := Algebra.ofId R _
@[expose] def u (A B:R) := left A B (InfinityChart318.x A B)
@[expose] def v (A B:R) := left A B (InfinityChart318.z A B)
@[expose] def x (A B:R) := right A B (ShortAffineJacobian318.x A B)
@[expose] def y (A B:R) := right A B (ShortAffineJacobian318.y A B)
@[expose] def parameter (A B:R) : PairRing A B := 1-coeff A B A*u A B*v A B-coeff A B B*v A B^2
@[expose] def denominator (A B:R) : PairRing A B := InfinityInputPolynomial318.denominator (parameter A B) (u A B) (x A B)
@[expose] def numeratorX (A B:R) : PairRing A B := InfinityInputPolynomial318.numeratorX (coeff A B A) (coeff A B B) (parameter A B) (u A B) (x A B) (y A B)
@[expose] def numeratorY (A B:R) : PairRing A B := InfinityInputPolynomial318.numeratorY (coeff A B A) (coeff A B B) (parameter A B) (u A B) (x A B) (y A B)

theorem left_relation (A B:R) : v A B-u A B^3-coeff A B A*u A B*v A B^2-coeff A B B*v A B^3=0 := by
  have h1 : left A B 1=1 := (left A B).toRingHom.map_one
  have hh:=congrArg (left A B) (InfinityChart318.relation A B)
  simpa only [map_sub,pow_succ,pow_zero,mul_one,h1,map_mul,map_zero,AlgHom.commutes,coeff,Algebra.ofId_apply,u,v] using hh
theorem right_relation (A B:R) : y A B^2-x A B^3-coeff A B A*x A B-coeff A B B=0 := by
  have h1 : right A B 1=1 := (right A B).toRingHom.map_one
  have hh:=congrArg (right A B) (ShortAffineJacobian318.relation A B)
  simpa only [map_sub,pow_succ,pow_zero,mul_one,h1,map_mul,map_zero,AlgHom.commutes,coeff,Algebra.ofId_apply,x,y] using hh

theorem parameter_relation (A B:R) : parameter A B^2*(1-parameter A B)-
    coeff A B A*u A B^4*parameter A B-coeff A B B*u A B^6=0 :=
by
  simpa only [parameter] using InfinityInputPolynomial318.parameter_relation (R:=PairRing A B)
    (coeff A B A) (coeff A B B) (u A B) (v A B) (left_relation A B)

theorem homogeneous_relation (A B:R) : numeratorY A B^2-numeratorX A B^3-
    coeff A B A*numeratorX A B*denominator A B^4-coeff A B B*denominator A B^6=0 :=
  InfinityInputPolynomial318.output_equation _ _ _ _ _ _ (right_relation A B) (parameter_relation A B)

abbrev OutputRing (A B:R) := Localization.Away (denominator A B)
@[expose] def pairMap (A B:R) : PairRing A B →ₐ[R] OutputRing A B :=
  IsScalarTower.toAlgHom R (PairRing A B) (OutputRing A B)
theorem denominator_unit (A B:R) : IsUnit (pairMap A B (denominator A B)) :=
  IsLocalization.Away.algebraMap_isUnit (S:=OutputRing A B) (denominator A B)
@[expose] def denominatorUnit (A B:R) : (OutputRing A B)ˣ := (denominator_unit A B).unit
@[expose] def outX (A B:R) : OutputRing A B := pairMap A B (numeratorX A B)*(↑(denominatorUnit A B)⁻¹)^2
@[expose] def outY (A B:R) : OutputRing A B := pairMap A B (numeratorY A B)*(↑(denominatorUnit A B)⁻¹)^3

/-- Literal finite output equation on a genuine open neighborhood of infinity times finite. -/
theorem output_equation (A B:R) : outY A B^2-outX A B^3-
    algebraMap R (OutputRing A B) A*outX A B-algebraMap R (OutputRing A B) B=0 := by
  have hh:=congrArg (pairMap A B) (homogeneous_relation A B)
  have hm (a:PairRing A B) (n:ℕ) : pairMap A B (a^n)=(pairMap A B a)^n := by
    induction n with
    | zero =>
        simp only [pow_zero]
        change algebraMap (PairRing A B) (OutputRing A B) 1=1
        exact (algebraMap (PairRing A B) (OutputRing A B)).map_one
    | succ n ih => simp only [pow_succ,map_mul,ih]
  simp only [map_sub,hm,map_mul,map_zero,coeff,Algebra.ofId_apply,AlgHom.commutes] at hh
  have hk : pairMap A B (denominator A B)*↑(denominatorUnit A B)⁻¹=1 := by
    rw [←(denominator_unit A B).unit_spec]
    exact Units.mul_inv _
  change (pairMap A B (numeratorY A B)*(↑(denominatorUnit A B)⁻¹)^3)^2-
    (pairMap A B (numeratorX A B)*(↑(denominatorUnit A B)⁻¹)^2)^3-
    algebraMap R (OutputRing A B) A*(pairMap A B (numeratorX A B)*(↑(denominatorUnit A B)⁻¹)^2)-
    algebraMap R (OutputRing A B) B=0
  calc
    _=(↑(denominatorUnit A B)⁻¹)^6*(pairMap A B (numeratorY A B)^2-
      pairMap A B (numeratorX A B)^3-algebraMap R (OutputRing A B) A*pairMap A B (numeratorX A B)*pairMap A B (denominator A B)^4-
      algebraMap R (OutputRing A B) B*pairMap A B (denominator A B)^6)+
      algebraMap R (OutputRing A B) A*pairMap A B (numeratorX A B)*(↑(denominatorUnit A B)⁻¹)^2*((pairMap A B (denominator A B)*↑(denominatorUnit A B)⁻¹)^4-1)+
      algebraMap R (OutputRing A B) B*((pairMap A B (denominator A B)*↑(denominatorUnit A B)⁻¹)^6-1) := by ring
    _=0 := by rw [hh,hk]; ring

@[expose] def outputMap (A B:R) : ShortAffineJacobian318.Ring A B →ₐ[R] OutputRing A B :=
  AffineEquationFunctor318.toHom A B ⟨(outX A B,outY A B),output_equation A B⟩
@[simp] theorem outputMap_x (A B:R) : outputMap A B (ShortAffineJacobian318.x A B)=outX A B := AffineEquationFunctor318.toHom_x ..
@[simp] theorem outputMap_y (A B:R) : outputMap A B (ShortAffineJacobian318.y A B)=outY A B := AffineEquationFunctor318.toHom_y ..

end InfinityInputAlgebra318
