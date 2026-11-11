module
public import LinearRootCoordinate318
public import Mathlib.RingTheory.DedekindDomain.Different
public section
noncomputable section
namespace ActualLinearRootDifferent318
open Polynomial QuadraticPresentation318 LinearRootCoordinate318 Module
attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra
variable (a:ℂ)
abbrev P:=ℂ[X]
abbrev B:=LinearRootCoordinate318.Root (1:ℂˣ) a
@[expose] def root:B a:=AdjoinRoot.root (polynomial (parameter (1:ℂˣ) a))
@[expose] def equation:P[X]:=polynomial (parameter (1:ℂˣ) a)
local instance domain:IsDomain (B a):=
  Function.Injective.isDomain (coordinateEquiv (1:ℂˣ) a).toRingHom
    (coordinateEquiv (1:ℂˣ) a).injective
@[expose] def basis:Basis (Fin 2) P (B a):=
  (QuadraticAlgebra.basis (parameter (1:ℂˣ) a) 0).map
    (presentationEquiv (parameter (1:ℂˣ) a)).toLinearEquiv
lemma basis_zero:basis a 0=1:=by
  simp only [basis,Basis.map_apply,QuadraticAlgebra.basis_apply_zero,
    AlgEquiv.toLinearEquiv_apply,map_one]
lemma basis_one:basis a 1=root a:=by
  simp only [basis,Basis.map_apply,QuadraticAlgebra.basis_apply_one,
    AlgEquiv.toLinearEquiv_apply,presentationEquiv_generator,root]
local instance free:Module.Free P (B a):=.of_basis (basis a)
local instance finite:Module.Finite P (B a):=.of_basis (basis a)
@[expose] def powerBasis:PowerBasis P (B a) where
  gen:=root a
  dim:=2
  basis:=basis a
  basis_eq_pow i:=by fin_cases i <;> simp [basis_zero,basis_one]

/-- This is the original linear-root ring, not a completed formal copy.
Its coordinate isomorphism derives normality; the finite polynomial
base action remains t = z² + a throughout. -/
lemma dedekind:IsDedekindDomain (B a):=by
  letI:IsIntegrallyClosed (B a):=
    IsIntegrallyClosed.of_equiv (coordinateEquiv (1:ℂˣ) a).symm.toRingEquiv
  letI:IsNoetherianRing (B a):=IsNoetherianRing.of_finite P (B a)
  letI:Algebra.IsIntegral P (B a):=Algebra.IsIntegral.of_finite P (B a)
  letI:Ring.DimensionLEOne (B a):=Ring.DimensionLEOne.of_isIntegral P (B a)
  exact { (inferInstance:IsDomain (B a)),(inferInstance:IsNoetherianRing (B a)),
    (inferInstance:IsIntegrallyClosed (B a)),(inferInstance:Ring.DimensionLEOne (B a)) with }
local instance dedekindInstance:IsDedekindDomain (B a):=dedekind a
lemma root_equation:Polynomial.aeval (root a) (equation a)=0:=by
  simp only [equation,polynomial,map_sub,map_pow,Polynomial.aeval_X,Polynomial.aeval_C]
  exact sub_eq_zero.mpr (root_square (parameter (1:ℂˣ) a))
lemma monic:(equation a).Monic:=Polynomial.monic_X_pow_sub_C _ (by decide)
lemma degree_two:(equation a).degree=2:=by
  rw [Polynomial.degree_eq_natDegree (monic a).ne_zero]
  simp [equation,polynomial,Polynomial.natDegree_X_pow_sub_C]
lemma minpoly_root:minpoly P (root a)=equation a:=by
  apply minpoly.eq_of_linearIndependent P (root a) (monic a) (root_equation a) 2 (degree_two a)
  have he:(fun i:Fin 2=>(root a)^i.val)=basis a:=by
    funext i
    exact ((powerBasis a).basis_eq_pow i).symm
  rw [he]
  exact (basis a).linearIndependent
lemma derivative_value:
    Polynomial.aeval (root a) (Polynomial.derivative (minpoly P (root a)))=2*root a:=by
  rw [minpoly_root]
  norm_num [equation,polynomial,Polynomial.derivative_pow]
  exact Or.inl (map_ofNat (algebraMap P (B a)) 2)
@[expose] def fieldBasis:Basis (Fin 2) (FractionRing P) (FractionRing (B a)):=
  (basis a).localizationLocalization (FractionRing P) (nonZeroDivisors P) (FractionRing (B a))
@[expose] def fieldPowerBasis:PowerBasis (FractionRing P) (FractionRing (B a)) where
  gen:=algebraMap (B a) (FractionRing (B a)) (root a)
  dim:=2
  basis:=fieldBasis a
  basis_eq_pow i:=by
    fin_cases i <;> simp [fieldBasis,Basis.localizationLocalization_apply,basis_zero,basis_one]

/-- Exact trace-defined different of the genuine intermediate branch
ring. The monogenic conductor is proved top from its actual power basis;
the generator is twice the ORIGINAL signed root. -/
theorem different_eq:
    differentIdeal P (B a)=Ideal.span {2*root a}:=by
  have he:=conductor_mul_differentIdeal P (FractionRing P) (FractionRing (B a))
    (root a) (show Algebra.adjoin (FractionRing P)
      {algebraMap (B a) (FractionRing (B a)) (root a)}=⊤ from
        (fieldPowerBasis a).adjoin_gen_eq_top)
  have hc := conductor_eq_top_of_powerBasis (powerBasis a)
  change conductor P (root a) = ⊤ at hc
  rw [hc,Ideal.top_mul,derivative_value] at he
  exact he
lemma simple_different:
    differentIdeal P (B a)=Ideal.span {root a}:=by
  rw [different_eq]
  have h2:IsUnit (2:B a):=by
    simpa only [map_ofNat] using (IsUnit.mk0 (2:ℂ) (by norm_num)).map (algebraMap ℂ (B a))
  rw [Ideal.span_singleton_mul_left_unit h2]
end ActualLinearRootDifferent318
