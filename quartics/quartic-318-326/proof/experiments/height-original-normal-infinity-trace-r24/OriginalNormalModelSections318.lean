module
public import OriginalNormalModelCanonicalIso318
public import IsoOverBaseSections318
public import IntegralNormalizationConductorChart318
public section
noncomputable section
namespace OriginalNormalModelSections318
open AlgebraicGeometry CategoryTheory NumberField Polynomial
open OriginalPointFinitePlaceRoots318 OriginalAllPlaceNormalizedData318 OriginalAllPlaceNormalModel318
open IntegralDistinctContactOpen318
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency.types false
variable (c : Fin 4 → ℚˣ) (t : ℚ) (w : FinitePlace (K c t))
  (D : OriginalAllPlaceNormalizedData318.Data c t w) (M : Realization c t w D)
local notation "R" => V c t w
local notation "a" => contacts c t w
local notation "B" => SourceOpenRing c t w D
local notation "N" => arithmeticDenominator R D.coefficients
local instance sourceDomain : IsDomain B :=
  open_domain R a D.coefficients (K c t) (IsFractionRing.injective R (K c t))
    (contacts_injective c t w) (coefficients_ne_zero c t w D)
local instance : Module.Finite (Base R a D.coefficients) B :=
  (finite_free_etale R a D.coefficients).1
local instance : Algebra.Etale (Base R a D.coefficients) B :=
  (finite_free_etale R a D.coefficients).2.2

/-- Both actual base-chart section rings on the original realization
are transported by the same canonical isomorphism, not separately chosen. -/
@[expose] def chartEquiv (j : Fin 2) :
    Γ(M.scheme,M.projection ⁻¹ᵁ (IntegralTwoChartNormalization318.targetCover R j).1) ≃+*
      IntegralTwoChartNormalization318.chartRing R a N B j :=
  IsoOverBaseSections318.sections (OriginalNormalModelCanonicalIso318.iso c t w D M)
    (IntegralTwoChartNormalization318.modelMap R a N B) M.projection
    (OriginalNormalModelCanonicalIso318.base c t w D M)
    (IntegralTwoChartNormalization318.targetCover R j).1

/-- Remove the induced-algebra notation explicitly: the finite scalar
is the literal inherited polynomial algebra used by the codifferent. -/
@[expose] def canonicalFiniteEquiv :
    IntegralTwoChartNormalization318.chartRing R a N B 1 ≃+*
      IntegralFourRootNormalizationConductor318.normalOrder R a D.coefficients := by
  have hα : (IntegralReciprocalNormalClosures318.finitePolynomialMap R a N B).toAlgebra=
      (inferInstance : Algebra R[X] B) := by
    rw [IntegralNormalizationConductorChart318.scalarMap_eq]
    exact toAlgebra_algebraMap (R:=R[X]) (S:=B)
  have e := IntegralNormalizationConductorChart318.finiteChartClosureEquiv R a D.coefficients
  exact hα ▸ e

/-- The entire finite-base chart of M, which supplied the closed-center
cotangent construction, is now identified with the actual normal order
used by conductor and trace-dual calculations. No regularity is inferred. -/
@[expose] def finiteEquiv :
    Γ(M.scheme,M.projection ⁻¹ᵁ (IntegralTwoChartNormalization318.targetCover R 1).1) ≃+*
      IntegralFourRootNormalizationConductor318.normalOrder R a D.coefficients :=
  (chartEquiv c t w D M 1).trans (canonicalFiniteEquiv c t w D)
end OriginalNormalModelSections318
