module
public import IntegralNormalFiniteDualSheafRestriction318
public import IntegralNormalInfinityDualSheafRestriction318
public import OriginalNormalInfinityDuality318
public section
noncomputable section
namespace OriginalNormalDualNativeRestrictions318
open NumberField Polynomial AlgebraicGeometry CategoryTheory
open OriginalPointFinitePlaceRoots318 OriginalAllPlaceNormalizedData318 OriginalAllPlaceNormalModel318
variable (c : Fin 4 → ℚˣ) (t : ℚ) (w : FinitePlace (K c t))
  (D : OriginalAllPlaceNormalizedData318.Data c t w)
local notation "R" => V c t w
local notation "a" => contacts c t w
local notation "d" => D.coefficients
local notation "B" => SourceOpenRing c t w D

/-- Native restriction of the exact original finite trace-codifferent,
with the original all-place normalized coefficients. -/
@[expose] def finiteIso :
    (Scheme.Modules.restrictFunctor
      (IntegralNormalFiniteDualSheafRestriction318.map R a d)).obj
      (IntegralNormalTraceSheafDuality318.traceSheaf R a d) ≅
        IntegralNormalFiniteDualSheafRestriction318.overlapDual R a d := by
  letI : IsDomain B := IntegralDistinctContactOpen318.open_domain R a d (K c t)
    (IsFractionRing.injective R (K c t)) (contacts_injective c t w)
    (coefficients_ne_zero c t w D)
  exact IntegralNormalFiniteDualSheafRestriction318.traceRestrictionIso R a d
    (coefficients_ne_zero c t w D)

/-- Native restriction of the OLD actual original infinity dualSheaf.
Its scalar is the existing reciprocalPolynomialMap, not the finite one. -/
@[expose] def infinityIso :
    (Scheme.Modules.restrictFunctor
      (IntegralNormalInfinityDualSheafRestriction318.map R a d)).obj
      (OriginalNormalInfinityDuality318.dualSheaf c t w D) ≅
        IntegralNormalInfinityDualSheafRestriction318.overlapDual R a d := by
  letI : IsDomain B := IntegralDistinctContactOpen318.open_domain R a d (K c t)
    (IsFractionRing.injective R (K c t)) (contacts_injective c t w)
    (coefficients_ne_zero c t w D)
  exact IntegralNormalInfinityDualSheafRestriction318.restrictionIso R a d
    (coefficients_ne_zero c t w D)
end OriginalNormalDualNativeRestrictions318
