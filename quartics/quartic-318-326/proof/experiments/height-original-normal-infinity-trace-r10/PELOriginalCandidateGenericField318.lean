module
public import PELOriginalProjectedGenericFinite318
public import ActualOpenFractionField318
public section
noncomputable section
namespace PELOriginalCandidateGenericField318
open AlgebraicGeometry CategoryTheory
open QuaternionicRealPeriod318 PELOriginalLevelTheta318 PELOriginalLevelPowerSections318
open PELOriginalReducedProjectiveCandidate318 PELOriginalCandidateAffineCharts318
open PELOriginalCandidateNineChartCover318 PELOriginalProjectedGenericFinite318
variable (τ:ℂ)(hτ:0<τ.im)(j:Label 3)
local instance candidateIntegral:IsIntegral (candidate τ hτ):=
  PELOriginalCandidateIntegral318.integral τ hτ
local instance chartDomain:IsDomain (CoordinateChart τ hτ j):=
  PELOriginalCandidateChartDomains318.coordinate_chart_domain τ hτ j

/-- The coefficient map is induced by the SAME actual open immersion
and actual affine generic-stalk map, not chosen from an abstract field
isomorphism. -/
@[expose,instance_reducible] def chartAlgebra:
    Algebra (CoordinateChart τ hτ j) (candidate τ hτ).functionField:=
  ActualOpenFractionField318.sourceAlgebra (chartMap τ hτ j)
attribute [local instance] chartAlgebra
@[expose] def comparison:
    (candidate τ hτ).functionField≃ₐ[CoordinateChart τ hτ j]actualChartFunctionField τ hτ j:=
  ActualOpenFractionField318.equiv (chartMap τ hτ j) (actualChartFunctionField τ hτ j)
lemma on_actual_coefficient(a:CoordinateChart τ hτ j):
    comparison τ hτ j (algebraMap (CoordinateChart τ hτ j) (candidate τ hτ).functionField a)=
      algebraMap (CoordinateChart τ hτ j) (actualChartFunctionField τ hτ j) a:=
  (comparison τ hτ j).commutes a

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra
/-- The specified rational projection acts through that exact genuine
chart-field identification. The coordinate theorem below pins BOTH
variables to actual original generic section germs. -/
@[expose,instance_reducible] def projectedAlgebra(x:ComplexVectors):
    Algebra (projectedRationalBase τ hτ j x) (candidate τ hτ).functionField:=
  ((comparison τ hτ j).symm.toRingHom.comp
    (algebraMap (projectedRationalBase τ hτ j x) (actualChartFunctionField τ hτ j))).toAlgebra
@[expose] def projectedComparison(x:ComplexVectors):
    letI:=projectedAlgebra τ hτ j x
    (candidate τ hτ).functionField≃ₐ[projectedRationalBase τ hτ j x]
      actualChartFunctionField τ hτ j:=by
  letI:=projectedAlgebra τ hτ j x
  exact {(comparison τ hτ j).toRingEquiv with
    commutes':=by intro c;exact (comparison τ hτ j).apply_symm_apply _}

/-- The formal rational variables map to the actual projected ratio
section germs in the WHOLE original candidate's generic stalk. -/
theorem on_projected_coordinate(x:ComplexVectors)(hx:value τ hτ 3 j x≠0)(k:Fin 2):
    letI:=projectedAlgebra τ hτ j x
    algebraMap (projectedRationalBase τ hτ j x) (candidate τ hτ).functionField
      (rationalEquivalence τ hτ j x hx
        (algebraMap (MvPolynomial (Fin 2) ℂ) _ (MvPolynomial.X k)))=
      algebraMap (CoordinateChart τ hτ j) (candidate τ hτ).functionField
        (PELOriginalProjectedChartIndependence318.projectedFunction τ hτ x j k):=by
  letI:=projectedAlgebra τ hτ j x
  apply (projectedComparison τ hτ j x).injective
  rw [AlgEquiv.commutes]
  change _=comparison τ hτ j _
  rw [on_actual_coefficient]
  exact rational_coordinate τ hτ j x hx k

/-- Genuine finite generic degree for the WHOLE actual candidate field,
with the produced actual projection scalar action, not a canonical
self-field module or an unrelated rational-coordinate structure. -/
theorem whole_generic_finite(x:ComplexVectors)(hx:value τ hτ 3 j x≠0):
    letI:=projectedAlgebra τ hτ j x
    Module.Finite (projectedRationalBase τ hτ j x) (candidate τ hτ).functionField:=by
  letI:=projectedAlgebra τ hτ j x
  letI:Module.Finite (projectedRationalBase τ hτ j x) (actualChartFunctionField τ hτ j):=
    actual_finite_generic_degree τ hτ j x hx
  exact Module.Finite.equiv (projectedComparison τ hτ j x).symm.toLinearEquiv
end PELOriginalCandidateGenericField318
