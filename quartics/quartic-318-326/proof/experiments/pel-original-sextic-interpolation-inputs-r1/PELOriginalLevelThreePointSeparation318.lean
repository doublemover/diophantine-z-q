module
public import PELOriginalTripleExponentialTranslate318
public import PELOriginalThetaTranslationPeriod318
public section
noncomputable section
namespace PELOriginalLevelThreePointSeparation318
open QuaternionicRealPeriod318 DiscreteComplexPeriodAtlas318
open PELOriginalPolarizationTransitions318 PELOriginalAllLevelProjectiveMap318
variable (τ:ℂ)(hτ:0<τ.im)

/-- The SAME nine original level-three sections separate actual points:
projective equality supplies a triple-product identity, its derived entire
translate law forces an ORIGINAL lattice period, and only then are the
original quotient points identified. No tangent or embedding assertion. -/
theorem original_lifts_equal(x y:ComplexVectors)
    (h:projectiveMap τ hτ 1 (projection (P τ) x)=
      projectiveMap τ hτ 1 (projection (P τ) y)):
    projection (P τ) x=projection (P τ) y:=by
  obtain ⟨C,hC,l,hl⟩:=PELOriginalTripleExponentialTranslate318.produced_translate τ hτ x y h
  exact PELOriginalThetaTranslationPeriod318.original_points_equal τ hτ x y C hC l hl

/-- Genuine point injectivity on the original compact complex torus,
not an injectivity statement on a chosen fundamental region. -/
theorem injective:Function.Injective (projectiveMap τ hτ 1):=by
  intro p q
  refine Quotient.inductionOn₂ p q ?_
  intro x y h
  exact original_lifts_equal τ hτ x y h
end PELOriginalLevelThreePointSeparation318
