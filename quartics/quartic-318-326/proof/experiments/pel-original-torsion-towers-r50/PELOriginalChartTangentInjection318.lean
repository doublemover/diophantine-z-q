module
public import PELOriginalChartTangentDerivation318
public import Mathlib.Analysis.Calculus.FDeriv.Prod
public section
noncomputable section
namespace PELOriginalChartTangentInjection318
open QuaternionicRealPeriod318 PELOriginalLevelTheta318 PELOriginalLevelPowerSections318
open PELOriginalCandidateAffineCharts318 PELOriginalChartAnalyticEvaluation318
open PELOriginalAllLevelHolomorphicMap318 PELOriginalChartTangentDerivation318
open ComplexProjectiveComplexAtlas318
variable (τ : ℂ) (hτ : 0 < τ.im) (x : ComplexVectors) (j : Label 3)
  (hj : value τ hτ 3 j x ≠ 0)
/-- Equality of derivations on the WHOLE actual chart forces equality
of the original analytic ratio derivatives. Every ratio is an actual
coordinate-ring element, and no tangent relation is omitted. -/
lemma ratio_derivative_eq (v w : ComplexVectors)
    (he : tangentDerivation τ hτ x j hj v = tangentDerivation τ hτ x j hj w) :
    fderiv ℂ (ratioVector τ hτ 1 j) x v = fderiv ℂ (ratioVector τ hτ 1 j) x w := by
  let Q : ComplexVectors → ({i : Label 3 // i ≠ j} → ℂ) :=
    fun z i => value τ hτ 3 i.val z/value τ hτ 3 j z
  let e : ({i : Label 3 // i ≠ j} → ℂ) ≃L[ℂ] TargetModel 1 :=
    (coordinates (Label 3) (0 : Label 3) j).toContinuousLinearEquiv
  have hdQ : DifferentiableAt ℂ Q x := by
    apply differentiableAt_pi.mpr
    intro i
    exact (PELOriginalLevelPowerSections318.holomorphic τ hτ 3 i.val x).div
      (PELOriginalLevelPowerSections318.holomorphic τ hτ 3 j x) hj
  have hQ : fderiv ℂ Q x v = fderiv ℂ Q x w := by
    funext i
    have h := congrArg (fun d => d (ratioElement τ hτ j i.val)) he
    rw [tangentDerivation_ratio,tangentDerivation_ratio] at h
    change fderiv ℂ (fun z => Q z i) x v = fderiv ℂ (fun z => Q z i) x w at h
    simp only [fderiv_apply hdQ i,ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.proj_apply] at h
    exact h
  have hD : fderiv ℂ (ratioVector τ hτ 1 j) x =
      e.toContinuousLinearMap.comp (fderiv ℂ Q x) :=
    (e.toContinuousLinearMap.hasFDerivAt.comp x hdQ.hasFDerivAt).fderiv
  rw [hD]
  exact congrArg e hQ
/-- The actual analytic tangent space injects into derivations of the
WHOLE original algebraic candidate chart at its genuine complex point.
This does NOT assert the converse or infer algebraic smoothness from
closed-point/image equality. -/
theorem tangentDerivation_injective :
    Function.Injective (tangentDerivation τ hτ x j hj) := by
  intro v w he
  exact PELOriginalLevelThreeTangentSeparation318.chart_derivative_injective τ hτ x j hj
    (ratio_derivative_eq τ hτ x j hj v w he)
end PELOriginalChartTangentInjection318
