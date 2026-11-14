module
public import FourRootInfinityTensorPresentation318
public import FourRootAffineSmooth318
public import FourRootCoordinateOverlap318
public import Mathlib.RingTheory.Flat.TorsionFree
public section
noncomputable section
namespace FourRootInfinityDomain318
open Polynomial
open FourRootCoordinateOverlap318
variable (b:Fin 4→ℂ) (hb:Function.Injective b)
abbrev P:=Polynomial ℂ
local instance polyAlgebra:Algebra P (Infinity b):=
  (Polynomial.aeval (FourRootInfinityCoordinateRing318.coordinate b none)).toAlgebra
local instance polyTower:IsScalarTower ℂ P (Infinity b):=by
  apply IsScalarTower.of_algebraMap_eq
  intro c
  exact (Polynomial.aeval_C _ c).symm

/-- The actual normalized coordinate u is a nonzero divisor because the
WHOLE infinity quotient is free over the same polynomial u-base. -/
theorem u_regular:FourRootInfinityCoordinateRing318.coordinate b none∈nonZeroDivisors (Infinity b):=by
  letI:Module.Free P (Infinity b):=(FourRootInfinityTensorPresentation318.finite_free b).2
  letI:Module.IsTorsionFree P (Infinity b):=inferInstance
  rw [mem_nonZeroDivisors_iff_left]
  intro r hr
  have hs:(X:P) • r=0:=by
    change algebraMap P (Infinity b) X*r=0
    rw [FourRootInfinityTensorPresentation318.base_X]
    exact hr
  exact (smul_eq_zero.mp hs).resolve_left Polynomial.X_ne_zero

theorem localization_injective:Function.Injective
    (algebraMap (Infinity b) (InfinityOverlap b)):=by
  apply IsLocalization.injective (M:=Submonoid.powers (FourRootInfinityCoordinateRing318.coordinate b none))
  rintro q ⟨n,rfl⟩
  exact (nonZeroDivisors (Infinity b)).pow_mem (u_regular b) n

lemma finite_root_ne_zero (k:Fin 4):FourRootAffineCoordinateRing318.coordinate b (some k)≠0:=by
  intro h
  have hg:FourRootOrderSigns318.generator (FourRootAffineTensorPresentation318.radicand b) k=0:=by
    have he:=congrArg (FourRootAffineTensorPresentation318.toTensor b) h
    simpa only [FourRootAffineTensorPresentation318.toTensor_root,map_zero] using he
  letI:IsDomain (FourRootAffineTensorPresentation318.TensorRing b):=
    FourRootActualGenericField318.tensor_domain b hb
  letI:Module.Free P (FourRootAffineTensorPresentation318.TensorRing b):=
    (FourRootOrder318.finite_free (FourRootAffineTensorPresentation318.radicand b)).2
  have hinj:=FaithfulSMul.algebraMap_injective P (FourRootAffineTensorPresentation318.TensorRing b)
  have he:=FourRootOrderSigns318.generator_square (FourRootAffineTensorPresentation318.radicand b) k
  rw [hg,zero_pow (by decide:2≠0)] at he
  have hz:FourRootAffineTensorPresentation318.radicand b k=0:=hinj (he.symm.trans (map_zero _).symm)
  exact Polynomial.X_sub_C_ne_zero (b k) hz

theorem finite_overlap_domain:IsDomain (AffineOverlap b):=by
  letI:IsDomain (Affine b):=FourRootActualGenericField318.affine_domain b hb
  exact IsLocalization.Away.isDomain (AffineOverlap b) (finite_root_ne_zero b hb 0)
theorem infinity_overlap_domain:IsDomain (InfinityOverlap b):=by
  letI:IsDomain (AffineOverlap b):=finite_overlap_domain b hb
  exact Function.Injective.isDomain (FourRootCoordinateOverlap318.overlapEquiv b)
    (FourRootCoordinateOverlap318.overlapEquiv b).injective

/-- No component supported over u=0 is discarded. Actual injectivity into
its literal principal open proves the whole infinity quotient is a domain. -/
theorem infinity_domain:IsDomain (Infinity b):=by
  letI:IsDomain (InfinityOverlap b):=infinity_overlap_domain b hb
  exact Function.Injective.isDomain (algebraMap (Infinity b) (InfinityOverlap b))
    (localization_injective b)
end FourRootInfinityDomain318
