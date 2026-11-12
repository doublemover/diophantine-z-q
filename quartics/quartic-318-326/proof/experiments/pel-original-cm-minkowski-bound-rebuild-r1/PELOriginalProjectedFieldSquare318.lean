module
public import PELOriginalPrimitiveGeneratorExpressions318
public import PELOriginalFiniteOpenProduct318
public import FractionPrincipalCompatibility318
public section
noncomputable section
namespace PELOriginalProjectedFieldSquare318
open QuaternionicRealPeriod318 PELOriginalLevelTheta318 PELOriginalLevelPowerSections318
open PELOriginalCandidateAffineCharts318 PELOriginalProjectedGenericFinite318
open PELOriginalProjectedPrimitivePolynomial318 PELOriginalProjectedChartIndependence318
open PELOriginalProjectedFiniteOpen318
variable (τ:ℂ)(hτ:0<τ.im)(j:Label 3)(x:ComplexVectors)(hx:value τ hτ 3 j x≠0)
local instance chartDomain:IsDomain (CoordinateChart τ hτ j):=
  PELOriginalCandidateChartDomains318.coordinate_chart_domain τ hτ j
attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra
/-- The fixed rational-coordinate embedding into the SAME candidate
chart field. It is determined before any localization denominator. -/
@[expose] def rationalEmbedding:FractionRing BasePolynomial→+*OriginalField τ hτ j:=
  (algebraMap (BaseField τ hτ j x) (OriginalField τ hτ j)).comp
    (rationalEquivalence τ hτ j x hx).toRingHom
/-- ALL polynomial coefficients, not only the two variables, commute
through the original independent-pair rational comparison. -/
theorem on_polynomial(p:BasePolynomial):
    rationalEmbedding τ hτ j x hx (algebraMap BasePolynomial (FractionRing BasePolynomial) p)=
      algebraMap (CoordinateChart τ hτ j) (OriginalField τ hτ j) (polynomialMap τ hτ j x p):=by
  rw [rationalEmbedding,RingHom.comp_apply,rationalEquivalence,
    IndependentPairGenericFinite318.rationalEquivalence,
    IsFractionRing.algEquivOfAlgEquiv_algebraMap]
  rw [←IsScalarTower.algebraMap_apply (projectedBase τ hτ j x)
      (BaseField τ hτ j x) (OriginalField τ hτ j),
    IsScalarTower.algebraMap_apply (projectedBase τ hτ j x)
      (CoordinateChart τ hτ j) (OriginalField τ hτ j)]
  congr 1
  exact (independent τ hτ x j hx).algebraMap_aevalEquiv p

/-- Exact whole localized coefficient square for the original base and
source rings. This makes field equality usable to prove ACTUAL order
identities after common-denominator restriction. -/
theorem localized_coefficient_square(d:BasePolynomial)(hd:d≠0)
    (ha:polynomialMap τ hτ j x d≠0):
    (FractionFiniteCoefficientLift318.toField (CoordinateChart τ hτ j)
      (OriginalField τ hτ j) (polynomialMap τ hτ j x d) ha).comp
        (Localization.awayMap (polynomialMap τ hτ j x).toRingHom d)=
    (rationalEmbedding τ hτ j x hx).comp
      (FractionFiniteCoefficientLift318.toField BasePolynomial (FractionRing BasePolynomial) d hd):=
  FractionPrincipalCompatibility318.base_field BasePolynomial (CoordinateChart τ hτ j)
    (FractionRing BasePolynomial) (OriginalField τ hτ j)
    (polynomialMap τ hτ j x).toRingHom (rationalEmbedding τ hτ j x hx)
    (on_polynomial τ hτ j x hx) d hd ha
end PELOriginalProjectedFieldSquare318
