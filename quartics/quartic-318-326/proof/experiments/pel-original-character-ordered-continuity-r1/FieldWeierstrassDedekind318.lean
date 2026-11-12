module
public import FieldBivariateIntegral318
public import Mathlib.RingTheory.Polynomial.Basic
public section
noncomputable section
namespace FieldWeierstrassDedekind318
open Polynomial
set_option maxHeartbeats 600000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {K:Type*} [Field K]
local notation "P" => Polynomial K
section Finite
variable (A B:K)
abbrev S:=ShortAffineJacobian318.Ring A B
local instance polyAlgebra:Algebra P (S A B):=(Polynomial.aeval (ShortAffineJacobian318.x A B)).toAlgebra
local instance polyTower:IsScalarTower K P (S A B):=by
  apply IsScalarTower.of_algebraMap_eq
  intro q
  exact (Polynomial.aeval_C _ q).symm
lemma finite_base_X:algebraMap P (S A B) X=ShortAffineJacobian318.x A B:=Polynomial.aeval_X _
lemma finite_base_C (q:K):algebraMap P (S A B) (C q)=algebraMap K (S A B) q:=Polynomial.aeval_C _ _
lemma finite_y_integral:IsIntegral P (ShortAffineJacobian318.y A B):=by
  refine ⟨(X^2-C (X^3+C A*X+C B):Polynomial P),Polynomial.monic_X_pow_sub_C _ (by decide:2≠0),?_⟩
  change Polynomial.aeval (ShortAffineJacobian318.y A B)
    (X^2-C (X^3+C A*X+C B):Polynomial P)=0
  simp only [map_sub,map_pow,map_add,map_mul,Polynomial.aeval_X,Polynomial.aeval_C,
    finite_base_X,finite_base_C]
  linear_combination ShortAffineJacobian318.relation A B
lemma finite_integral:Algebra.IsIntegral P (S A B):=by
  apply FieldBivariateIntegral318.quotient_integral
  intro i
  fin_cases i
  · change IsIntegral P (ShortAffineJacobian318.x A B)
    simpa only [finite_base_X] using (isIntegral_algebraMap (R:=P) (A:=S A B) (x:=X))
  · exact finite_y_integral A B
/-- The entire actual finite chart is Dedekind for every nonsingular
field-valued short model; no coefficient-nonzero hypothesis is added. -/
theorem affine (hD:IsUnit (-16*(4*A^3+27*B^2))):IsDedekindDomain (S A B):=by
  letI:=AffineCoordinateDomain318.affine_domain A B
  letI:=ShortAffineJacobian318.smooth A B hD
  letI:IsIntegrallyClosed (S A B):=SmoothDomainNormal318.integrallyClosed K (S A B)
  letI:=finite_integral A B
  letI:Ring.DimensionLEOne (S A B):=Ring.DimensionLEOne.of_isIntegral P (S A B)
  exact { (inferInstance:IsDomain (S A B)),(inferInstance:IsNoetherianRing (S A B)),
    (inferInstance:Ring.DimensionLEOne (S A B)),(inferInstance:IsIntegrallyClosed (S A B)) with }
end Finite
section Infinity
variable (A B:K)
abbrev I:=InfinityChart318.Ring A B
/-- Use z, not x, as the polynomial base. The equation is always monic
cubic in x, including when A=0 or B=0. -/
local instance infinityPolyAlgebra:Algebra P (I A B):=(Polynomial.aeval (InfinityChart318.z A B)).toAlgebra
local instance infinityPolyTower:IsScalarTower K P (I A B):=by
  apply IsScalarTower.of_algebraMap_eq
  intro q
  exact (Polynomial.aeval_C _ q).symm
lemma infinity_base_X:algebraMap P (I A B) X=InfinityChart318.z A B:=Polynomial.aeval_X _
lemma infinity_base_C (q:K):algebraMap P (I A B) (C q)=algebraMap K (I A B) q:=Polynomial.aeval_C _ _
lemma infinity_x_integral:IsIntegral P (InfinityChart318.x A B):=by
  refine ⟨(X^3+C (C A*X^2)*X+C (C B*X^3-X):Polynomial P),
    BivariateIntegral318.monic_cubic _ _,?_⟩
  change Polynomial.aeval (InfinityChart318.x A B)
    (X^3+C (C A*X^2)*X+C (C B*X^3-X):Polynomial P)=0
  simp only [map_add,map_mul,map_sub,map_pow,Polynomial.aeval_X,Polynomial.aeval_C,
    infinity_base_X,infinity_base_C]
  linear_combination -InfinityChart318.relation A B
lemma infinity_integral:Algebra.IsIntegral P (I A B):=by
  apply FieldBivariateIntegral318.quotient_integral
  intro i
  fin_cases i
  · exact infinity_x_integral A B
  · change IsIntegral P (InfinityChart318.z A B)
    simpa only [infinity_base_X] using (isIntegral_algebraMap (R:=P) (A:=I A B) (x:=X))
/-- Normality plus the literal monic-cubic dimension bound proves the
whole actual infinity chart Dedekind, not merely a smooth localization. -/
theorem infinity (hD:IsUnit (-16*(4*A^3+27*B^2))):IsDedekindDomain (I A B):=by
  letI:=InfinityCoordinateDomain318.infinity_domain A B
  letI:=InfinitySmooth318.smooth A B hD
  letI:IsIntegrallyClosed (I A B):=SmoothDomainNormal318.integrallyClosed K (I A B)
  letI:=infinity_integral A B
  letI:Ring.DimensionLEOne (I A B):=Ring.DimensionLEOne.of_isIntegral P (I A B)
  exact { (inferInstance:IsDomain (I A B)),(inferInstance:IsNoetherianRing (I A B)),
    (inferInstance:Ring.DimensionLEOne (I A B)),(inferInstance:IsIntegrallyClosed (I A B)) with }
end Infinity
end FieldWeierstrassDedekind318
