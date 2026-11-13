module
public import FourRootActualInfinityKaehler318
public import PolynomialRelativeCotangentFrame318
public section
noncomputable section
namespace FourRootActualRelativeCotangent318
open Polynomial
section Finite
variable (b:Fin 4→ℂ) (i:Fin 4)
abbrev F:=FourRootActualBranchKaehler318.SourceRing b i
local instance finiteBase:Algebra ℂ[X] (F b i):=
  (Polynomial.aeval (FourRootActualBranchKaehler318.sourceParameter b i)).toAlgebra
local instance finiteTower:IsScalarTower ℂ ℂ[X] (F b i):=by
  apply IsScalarTower.of_algebraMap_eq
  intro c
  exact (Polynomial.aeval_C _ c).symm
/-- The true finite relative cotangent module, for the original t-map,
has precisely the simple-root ideal as its annihilator up to the unit2. -/
theorem finite_annihilator (a:F b i):
    (∀ω:KaehlerDifferential ℂ[X] (F b i),a • ω=0)↔
      a∈(Ideal.span {2*FourRootActualBranchKaehler318.sourceCoordinate b i}:Ideal (F b i)):=by
  have h:=PolynomialRelativeCotangentFrame318.annihilator_iff
    (FourRootActualBranchKaehler318.sourceFrame b i) a
  simpa only [PolynomialRelativeCotangentFrame318.coefficient,Polynomial.aeval_X,
    FourRootActualBranchKaehler318.parameter_coefficient] using h
theorem finite_simple_annihilator (a:F b i):
    (∀ω:KaehlerDifferential ℂ[X] (F b i),a • ω=0)↔
      a∈(Ideal.span {FourRootActualBranchKaehler318.sourceCoordinate b i}:Ideal (F b i)):=by
  rw [finite_annihilator]
  have h2:IsUnit (2:F b i):=by
    simpa only [map_ofNat] using (IsUnit.mk0 (2:ℂ) (by norm_num)).map (algebraMap ℂ (F b i))
  rw [Ideal.span_singleton_mul_left_unit h2]
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
/-- The SAME statement at all eight infinity centers uses the actual
reciprocal projective scalar v=u², never the rank-eight u-base. -/
theorem infinity_annihilator (a:I b hb):
    (∀ω:KaehlerDifferential ℂ[X] (I b hb),a • ω=0)↔
      a∈(Ideal.span {2*FourRootActualInfinityKaehler318.coordinate b hb}:Ideal (I b hb)):=by
  have h:=PolynomialRelativeCotangentFrame318.annihilator_iff
    (FourRootActualInfinityKaehler318.frame b hb) a
  simpa only [PolynomialRelativeCotangentFrame318.coefficient,Polynomial.aeval_X,
    FourRootActualInfinityKaehler318.reciprocal_coefficient] using h
theorem infinity_simple_annihilator (a:I b hb):
    (∀ω:KaehlerDifferential ℂ[X] (I b hb),a • ω=0)↔
      a∈(Ideal.span {FourRootActualInfinityKaehler318.coordinate b hb}:Ideal (I b hb)):=by
  rw [infinity_annihilator]
  have h2:IsUnit (2:I b hb):=by
    simpa only [map_ofNat] using (IsUnit.mk0 (2:ℂ) (by norm_num)).map (algebraMap ℂ (I b hb))
  rw [Ideal.span_singleton_mul_left_unit h2]
end Infinity
end FourRootActualRelativeCotangent318
