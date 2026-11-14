module
public import PELOriginalProjectedChartIndependence318
public import PELOriginalAffineChartTranscendence318
public import PELOriginalCandidateChartBase318
public import IndependentPairGenericFinite318
public section
noncomputable section
namespace PELOriginalProjectedGenericFinite318
open QuaternionicRealPeriod318 PELOriginalLevelTheta318 PELOriginalLevelPowerSections318
open PELOriginalCandidateAffineCharts318 PELOriginalProjectedChartIndependence318
open PELOriginalChartSectionField318
variable (τ:ℂ)(hτ:0<τ.im)(j:Label 3)
local instance chartDomain:IsDomain (CoordinateChart τ hτ j):=
  PELOriginalCandidateChartDomains318.coordinate_chart_domain τ hτ j
local instance chartFiniteType:Algebra.FiniteType ℂ (CoordinateChart τ hτ j):=
  PELOriginalCandidateChartFiniteType318.finite_type τ hτ j
@[expose] def projectedBase(x:ComplexVectors):Subalgebra ℂ (CoordinateChart τ hτ j):=
  IndependentPairGenericFinite318.PolynomialBase (CoordinateChart τ hτ j)
    (projectedFunction τ hτ x j)
abbrev projectedRationalBase(x:ComplexVectors):=FractionRing (projectedBase τ hτ j x)
abbrev actualChartFunctionField:=FractionRing (CoordinateChart τ hτ j)
attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

/-- The rational base coordinates are precisely the two genuine local
analytic projected theta ratios, in the SAME actual affine chart. -/
@[expose] def rationalEquivalence(x:ComplexVectors)(hx:value τ hτ 3 j x≠0):
    FractionRing (MvPolynomial (Fin 2) ℂ)≃ₐ[ℂ]projectedRationalBase τ hτ j x:=
  IndependentPairGenericFinite318.rationalEquivalence (CoordinateChart τ hτ j)
    (projectedFunction τ hτ x j) (independent τ hτ x j hx)
theorem rational_coordinate(x:ComplexVectors)(hx:value τ hτ 3 j x≠0)(k:Fin 2):
    algebraMap (projectedRationalBase τ hτ j x) (actualChartFunctionField τ hτ j)
      (rationalEquivalence τ hτ j x hx
        (algebraMap (MvPolynomial (Fin 2) ℂ) _ (MvPolynomial.X k)))=
      algebraMap (CoordinateChart τ hτ j) (actualChartFunctionField τ hτ j)
        (projectedFunction τ hτ x j k):=
  IndependentPairGenericFinite318.rational_coordinate (CoordinateChart τ hτ j)
    (projectedFunction τ hτ x j) (independent τ hτ x j hx) k

/-- Every chosen original nonzero-coordinate point gives a genuine
FINITE function-field extension over its actual analytic projection
coordinates. No replacement Noether-normalization pair is used. -/
theorem actual_finite_generic_degree(x:ComplexVectors)(hx:value τ hτ 3 j x≠0):
    Module.Finite (projectedRationalBase τ hτ j x) (actualChartFunctionField τ hτ j):=
  IndependentPairGenericFinite318.finite_generic_degree (CoordinateChart τ hτ j)
    (projectedFunction τ hτ x j) (independent τ hτ x j hx)
    (PELOriginalAffineChartTranscendence318.actual_chart_trdeg_le_two τ hτ j)

/-- Every one of the nine full candidate charts has such a produced
finite generic projection, not merely a chart meeting an assumed image. -/
theorem every_chart_finite_generic:
    ∃x:ComplexVectors,AlgebraicIndependent ℂ (projectedFunction τ hτ x j)∧
      Module.Finite (projectedRationalBase τ hτ j x) (actualChartFunctionField τ hτ j):=by
  obtain ⟨x,hx⟩:=every_chart_independent τ hτ j
  refine ⟨x,hx,?_⟩
  exact IndependentPairGenericFinite318.finite_generic_degree (CoordinateChart τ hτ j)
    (projectedFunction τ hτ x j) hx
    (PELOriginalAffineChartTranscendence318.actual_chart_trdeg_le_two τ hτ j)
end PELOriginalProjectedGenericFinite318
