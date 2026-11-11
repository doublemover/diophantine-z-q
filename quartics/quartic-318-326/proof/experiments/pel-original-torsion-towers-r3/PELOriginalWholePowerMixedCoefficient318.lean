module
public import PELOriginalMixedPointEvaluation318
public import PELOriginalWholePowerRegularization318
public section
noncomputable section
namespace PELOriginalWholePowerMixedCoefficient318
open AlgebraicGeometry CategoryTheory QuaternionicRealPeriod318 DiscreteComplexPeriodAtlas318
open PELOriginalLevelTheta318 PELOriginalLevelPowerSections318
open PELOriginalCandidateAffineCharts318 PELOriginalCandidateNineChartCover318
open PELOriginalChartAnalyticEvaluation318 PELOriginalCandidateComplexPoints318
open PELOriginalReducedProjectiveCandidate318 PELOriginalMixedRatioCover318
open PELOriginalMixedPointEvaluation318
variable (τ : ℂ) (hτ : 0 < τ.im)
local instance candidateReduced : IsReduced (candidate τ hτ) := reduced τ hτ

open PELOriginalSectionMultiplication318
variable (m : ℕ)

/-- The whole chart regularization pulled to the actual mixed open. -/
@[expose] def coefficient (a : Index) (s : homogeneous τ hτ (3*m)) :
    Γ((mixedOpen τ hτ a).toScheme,⊤) :=
  (toAffine τ hτ a).appTop ((Scheme.ΓSpecIso (CommRingCat.of (CoordinateChart τ hτ a.1))).inv
    (PELOriginalWholePowerRegularization318.linear τ hτ m a.1 s))

lemma evaluation (a : Index) (s : homogeneous τ hτ (3*m))
    (p : Spec (CommRingCat.of ℂ) ⟶ (mixedOpen τ hτ a).toScheme)
    (z : ComplexVectors) (h3 : PELOriginalLevelPowerSections318.value τ hτ 3 a.1 z≠0)
    (he : p ≫ (mixedOpen τ hτ a).ι = candidateComplexPoint τ hτ (projection (P τ) z)) :
    (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (p.appTop (coefficient τ hτ m a s)) =
      PELOriginalWholePowerRatioCover318.coverRatio τ hτ m a.1 s z := by
  have hA : p ≫ toAffine τ hτ a =
      Spec.map (CommRingCat.ofHom (algebraEvaluation τ hτ z a.1 h3).toRingHom) := by
    apply (cancel_mono (chartMap τ hτ a.1)).1
    rw [Category.assoc,toAffine_chart,he,PELOriginalChartSchemePointIdentity318.chart_point]
  rw [coefficient,element_evaluation τ hτ a _ p z h3 hA,
    PELOriginalWholePowerRegularization318.cover_evaluation]
end PELOriginalWholePowerMixedCoefficient318
