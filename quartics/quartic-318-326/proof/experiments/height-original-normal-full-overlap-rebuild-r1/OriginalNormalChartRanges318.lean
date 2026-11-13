module
public import NormalizationClosureChartRange318
public import OriginalNormalOverlapChartMaps318
public section
noncomputable section
namespace OriginalNormalChartRanges318
open NumberField Polynomial AlgebraicGeometry CategoryTheory
open OriginalPointFinitePlaceRoots318 OriginalAllPlaceNormalizedData318 OriginalAllPlaceNormalModel318
open IntegralDistinctContactOpen318
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

lemma finite_canonical_range :
    letI := (OriginalNormalOrderChart318.canonicalData c t w D).isOpen
    (OriginalNormalOrderChart318.canonicalData c t w D).chart.opensRange=
      IntegralTwoChartNormalization318.modelMap R a N B ⁻¹ᵁ (JLineAtlas318.chart R 1 ''ᵁ ⊤) := by
  have hα : (IntegralReciprocalNormalClosures318.finitePolynomialMap R a N B).toAlgebra=
      (inferInstance : Algebra R[X] B) := by
    rw [IntegralNormalizationConductorChart318.scalarMap_eq]
    exact toAlgebra_algebraMap (R:=R[X]) (S:=B)
  have h := NormalizationClosureChartRange318.range
    (CommRingCat.ofHom (IntegralReciprocalNormalClosures318.finitePolynomialMap R a N B))
    (JLineAtlas318.chart R 1) (IntegralTwoChartNormalization318.coverMap R a N B)
    (IntegralTwoChartNormalization318.finite_factor R a N B)
  exact hα ▸ h

lemma infinity_canonical_range :
    letI := (OriginalNormalInfinityChart318.canonicalData c t w D).isOpen
    (OriginalNormalInfinityChart318.canonicalData c t w D).chart.opensRange=
      IntegralTwoChartNormalization318.modelMap R a N B ⁻¹ᵁ (JLineAtlas318.chart R 0 ''ᵁ ⊤) :=
  NormalizationClosureChartRange318.range
    (CommRingCat.ofHom (OriginalNormalInfinityOrder318.polynomialMap c t w D))
    (JLineAtlas318.chart R 0) (IntegralTwoChartNormalization318.coverMap R a N B)
    (IntegralTwoChartNormalization318.reciprocal_factor R a N B)

/-- The actual whole finite normal-order chart contains every point of M
above the finite base chart, including vertical and bad-prime points. -/
lemma finite_range : (OriginalNormalOrderChart318.chart c t w D M).opensRange=
    M.projection ⁻¹ᵁ (JLineAtlas318.chart R 1 ''ᵁ ⊤) := by
  letI := (OriginalNormalOrderChart318.canonicalData c t w D).isOpen
  exact NormalizationClosureChartRange318.transport _
    (OriginalNormalModelCanonicalIso318.iso c t w D M) _ _
    (OriginalNormalModelCanonicalIso318.base c t w D M) _
    (finite_canonical_range c t w D)

/-- Same full inverse-image assertion for the original reciprocal chart. -/
lemma infinity_range : (OriginalNormalInfinityChart318.chart c t w D M).opensRange=
    M.projection ⁻¹ᵁ (JLineAtlas318.chart R 0 ''ᵁ ⊤) := by
  letI := (OriginalNormalInfinityChart318.canonicalData c t w D).isOpen
  exact NormalizationClosureChartRange318.transport _
    (OriginalNormalModelCanonicalIso318.iso c t w D M) _ _
    (OriginalNormalModelCanonicalIso318.base c t w D M) _
    (infinity_canonical_range c t w D)
end OriginalNormalChartRanges318
