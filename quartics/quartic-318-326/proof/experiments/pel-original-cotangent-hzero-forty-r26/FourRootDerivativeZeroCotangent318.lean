module
public import FourRootRelativeCotangentQuotient318
public import FourRootDerivativeInfinityIdeal318
public section
noncomputable section
namespace FourRootDerivativeZeroCotangent318
open Polynomial KaehlerDifferential
open FourRootDerivativeZeroIdeals318
section Finite
variable (b:Fin 4→ℂ) (i:Fin 4)
abbrev F:=FourRootActualBranchKaehler318.SourceRing b i
local instance finiteBase:Algebra ℂ[X] (F b i):=
  (Polynomial.aeval (FourRootActualBranchKaehler318.sourceParameter b i)).toAlgebra
local instance finiteTower:IsScalarTower ℂ ℂ[X] (F b i):=by
  apply IsScalarTower.of_algebraMap_eq
  intro c
  exact (Polynomial.aeval_C _ c).symm
@[expose] def finiteZeroIdeal:Ideal (F b i):=
  (finiteIdeal b).map (algebraMap (FourRootAffineCoordinateRing318.Ring b) (F b i))
/-- The quotient by the restriction of the SAME whole finite zero ideal
is the actual relative cotangent module. The domain is not a replacement
ideal defined only from the relative module's annihilator. -/
@[expose] def finiteEquiv:
    (F b i⧸finiteZeroIdeal b i)≃ₗ[F b i]KaehlerDifferential ℂ[X] (F b i):=
  (Submodule.quotEquivOfEq _ _ (FourRootDerivativeFiniteIdeal318.derivative_ideal b i)).trans
    (FourRootRelativeCotangentQuotient318.finiteEquiv b i)
theorem finite_unit:
    finiteEquiv b i (Ideal.Quotient.mk (finiteZeroIdeal b i) 1)=
      D ℂ[X] (F b i) (FourRootActualBranchKaehler318.sourceCoordinate b i):=by
  simpa only [finiteEquiv,LinearEquiv.trans_apply,Submodule.quotEquivOfEq_mk] using
    FourRootRelativeCotangentQuotient318.finite_unit b i
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
@[expose] def infinityZeroIdeal:Ideal (I b hb):=
  (infinityIdeal b).map (algebraMap (FourRootInfinityCoordinateRing318.Ring b) (I b hb))
/-- The SAME infinity zero ideal gives the actual relative cotangent
module for v=u², throughout the genuine infinity canonical open. -/
@[expose] def infinityEquiv:
    (I b hb⧸infinityZeroIdeal b hb)≃ₗ[I b hb]KaehlerDifferential ℂ[X] (I b hb):=
  (Submodule.quotEquivOfEq _ _ (FourRootDerivativeInfinityIdeal318.derivative_ideal b hb)).trans
    (FourRootRelativeCotangentQuotient318.infinityEquiv b hb)
theorem infinity_unit:
    infinityEquiv b hb (Ideal.Quotient.mk (infinityZeroIdeal b hb) 1)=
      D ℂ[X] (I b hb) (FourRootActualInfinityKaehler318.coordinate b hb):=by
  simpa only [infinityEquiv,LinearEquiv.trans_apply,Submodule.quotEquivOfEq_mk] using
    FourRootRelativeCotangentQuotient318.infinity_unit b hb
end Infinity
end FourRootDerivativeZeroCotangent318
