module
public import FourRootActualRelativeCotangent318
public import PolynomialRelativeCotangentQuotient318
public section
noncomputable section
namespace FourRootRelativeCotangentQuotient318
open Polynomial KaehlerDifferential
open PolynomialRelativeCotangentFrame318 PolynomialRelativeCotangentQuotient318
section Finite
variable (b:Fin 4→ℂ) (i:Fin 4)
abbrev F:=FourRootActualBranchKaehler318.SourceRing b i
local instance finiteBase:Algebra ℂ[X] (F b i):=
  (Polynomial.aeval (FourRootActualBranchKaehler318.sourceParameter b i)).toAlgebra
local instance finiteTower:IsScalarTower ℂ ℂ[X] (F b i):=by
  apply IsScalarTower.of_algebraMap_eq
  intro c
  exact (Polynomial.aeval_C _ c).symm
lemma finite_coefficient:
    coefficient (FourRootActualBranchKaehler318.sourceFrame b i)=
      2*FourRootActualBranchKaehler318.sourceCoordinate b i:=by
  simpa only [coefficient,Polynomial.aeval_X] using
    FourRootActualBranchKaehler318.parameter_coefficient b i
/-- Genuine quotient presentation of the original finite relative
cotangent module over t, on its actual signed-root chart. -/
@[expose] def finiteEquiv:
    (F b i⧸(Ideal.span {2*FourRootActualBranchKaehler318.sourceCoordinate b i}:Ideal (F b i)))
      ≃ₗ[F b i]KaehlerDifferential ℂ[X] (F b i):=
  coefficientEquiv (FourRootActualBranchKaehler318.sourceFrame b i) _ (finite_coefficient b i)
/-- The quotient unit maps to dz_i, not a scalar multiple chosen after
the fact. This keeps the factor two in the defining relation. -/
theorem finite_unit:
    finiteEquiv b i (Ideal.Quotient.mk _ 1)=
      D ℂ[X] (F b i) (FourRootActualBranchKaehler318.sourceCoordinate b i):=by
  have h:=coefficientEquiv_differential
    (FourRootActualBranchKaehler318.sourceFrame b i) _ (finite_coefficient b i)
    (FourRootActualBranchKaehler318.sourceCoordinate b i)
  simpa only [FourRootActualBranchKaehler318.source_normalized,finiteEquiv] using h
end Finite
section Infinity
variable (b:Fin 4→ℂ) (hb:Function.Injective b)
abbrev I:=FourRootActualInfinityKaehler318.SourceRing b hb
local instance infinityBase:Algebra ℂ[X] (I b hb):=
  (Polynomial.aeval (FourRootActualInfinityKaehler318.reciprocalParameter b hb)).toAlgebra
local instance infinityTower:IsScalarTower ℂ ℂ[X] (I b hb):=by
  apply IsScalarTower.of_algebraMap_eq
  intro c
  exact (Polynomial.aeval_C _ c).symm
lemma infinity_coefficient:
    coefficient (FourRootActualInfinityKaehler318.frame b hb)=
      2*FourRootActualInfinityKaehler318.coordinate b hb:=by
  simpa only [coefficient,Polynomial.aeval_X] using
    FourRootActualInfinityKaehler318.reciprocal_coefficient b hb
/-- All eight infinity centers use the original reciprocal base v=u².
The rank-eight u-base is not substituted for the projective map. -/
@[expose] def infinityEquiv:
    (I b hb⧸(Ideal.span {2*FourRootActualInfinityKaehler318.coordinate b hb}:Ideal (I b hb)))
      ≃ₗ[I b hb]KaehlerDifferential ℂ[X] (I b hb):=
  coefficientEquiv (FourRootActualInfinityKaehler318.frame b hb) _ (infinity_coefficient b hb)
theorem infinity_unit:
    infinityEquiv b hb (Ideal.Quotient.mk _ 1)=
      D ℂ[X] (I b hb) (FourRootActualInfinityKaehler318.coordinate b hb):=by
  have h:=coefficientEquiv_differential
    (FourRootActualInfinityKaehler318.frame b hb) _ (infinity_coefficient b hb)
    (FourRootActualInfinityKaehler318.coordinate b hb)
  simpa only [FourRootActualInfinityKaehler318.coordinate_normalized,infinityEquiv] using h
end Infinity
end FourRootRelativeCotangentQuotient318
