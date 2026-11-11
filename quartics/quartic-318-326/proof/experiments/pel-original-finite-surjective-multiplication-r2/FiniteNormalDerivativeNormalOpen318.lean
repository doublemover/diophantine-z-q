module
public import IntegralConductorNormalOpen318
public import NormalPrimitiveFractionConductor318
public import WholeFiniteFractionExtension318
public section
noncomputable section
namespace FiniteNormalDerivativeNormalOpen318
open Polynomial
variable (R A : Type*) [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
  [CommRing A] [IsDomain A] [Algebra R A] [FaithfulSMul R A] [Module.Finite R A]
attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

/-- The whole derivative localization is integrally closed by the actual
primitive conductor, without invoking an unavailable general implication
from smoothness to normality or assuming the original chart is normal. -/
theorem integrallyClosed (t : A)
    (hprimitive : Function.Surjective
      (Polynomial.aeval (algebraMap A (FractionRing A) t) :
        Polynomial (FractionRing R) →ₐ[FractionRing R] FractionRing A))
    (hd : Polynomial.aeval t (minpoly R t).derivative ≠ 0) :
    IsIntegrallyClosed (Localization.Away (Polynomial.aeval t (minpoly R t).derivative)) := by
  apply IntegralConductorNormalOpen318.integrallyClosed A _ hd
  intro y hy
  exact NormalPrimitiveFractionConductor318.conductor R (FractionRing R) A (FractionRing A)
    t hprimitive y hy
end FiniteNormalDerivativeNormalOpen318
