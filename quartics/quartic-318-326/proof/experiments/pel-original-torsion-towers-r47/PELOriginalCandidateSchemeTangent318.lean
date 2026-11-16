module
public import PELOriginalChartTangentInjection318
public import EvaluationDualNumberLift318
public import PELOriginalCandidateChartBase318
public section
noncomputable section
namespace PELOriginalCandidateSchemeTangent318
open AlgebraicGeometry CategoryTheory
open QuaternionicRealPeriod318 PELOriginalLevelTheta318 PELOriginalLevelPowerSections318
open PELOriginalCandidateAffineCharts318 PELOriginalChartAnalyticEvaluation318
open PELOriginalReducedProjectiveCandidate318 PELOriginalChartTangentDerivation318
open EvaluationDualNumberLift318
variable (τ : ℂ) (hτ : 0 < τ.im) (x : ComplexVectors) (j : Label 3)
  (hj : value τ hτ 3 j x ≠ 0)
/-- The actual closed origin of the standard complex dual-number scheme. -/
@[expose] def origin : Spec (CommRingCat.of ℂ) ⟶ Spec (CommRingCat.of Dual) :=
  Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom)
/-- The existing original point in the actual candidate chart, included
through the genuine chart SCHEME isomorphism and open immersion. -/
@[expose] def center : Spec (CommRingCat.of ℂ) ⟶ candidate τ hτ :=
  Spec.map (CommRingCat.ofHom (algebraEvaluation τ hτ x j hj).toRingHom) ≫
    (actualChartIso τ hτ j).hom ≫ (candidateChart τ hτ j).ι
/-- A genuine dual-number SCHEME morphism into the same global reduced
candidate, produced from each original analytic tangent direction. -/
@[expose] def tangent (v : ComplexVectors) :
    Spec (CommRingCat.of Dual) ⟶ candidate τ hτ :=
  Spec.map (CommRingCat.ofHom
    (lift (algebraEvaluation τ hτ x j hj) (tangentDerivation τ hτ x j hj v)).toRingHom) ≫
    (actualChartIso τ hτ j).hom ≫ (candidateChart τ hτ j).ι
/-- Its closed origin is EXACTLY the original point, not a relabeled
closed point with the same cardinality or image. -/
theorem origin_tangent (v : ComplexVectors) : origin ≫ tangent τ hτ x j hj v = center τ hτ x j hj := by
  have hc : CommRingCat.ofHom
      (lift (algebraEvaluation τ hτ x j hj) (tangentDerivation τ hτ x j hj v)).toRingHom ≫
      CommRingCat.ofHom (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom =
      CommRingCat.ofHom (algebraEvaluation τ hτ x j hj).toRingHom :=
    congrArg (fun f : CoordinateChart τ hτ j →ₐ[ℂ] ℂ => CommRingCat.ofHom f.toRingHom)
      (constant_term (algebraEvaluation τ hτ x j hj) (tangentDerivation τ hτ x j hj v))
  rw [origin,tangent,center,←Category.assoc,←Spec.map_comp,hc]
/-- The genuine infinitesimal morphism fixes the original complex base
structure. This is stronger than being an unbased scheme morphism. -/
theorem tangent_over_complex (v : ComplexVectors) :
    tangent τ hτ x j hj v ≫ PELOriginalProperComplexCandidate318.structureMap τ hτ =
      Spec.map (CommRingCat.ofHom (algebraMap ℂ Dual)) := by
  change (Spec.map (CommRingCat.ofHom
      (lift (algebraEvaluation τ hτ x j hj) (tangentDerivation τ hτ x j hj v)).toRingHom) ≫
    PELOriginalCandidateNineChartCover318.chartMap τ hτ j) ≫
      PELOriginalProperComplexCandidate318.structureMap τ hτ = _
  rw [Category.assoc,PELOriginalCandidateChartBase318.chart_over_complex_base,←Spec.map_comp]
  congr 1
  ext c
  exact (lift (algebraEvaluation τ hτ x j hj) (tangentDerivation τ hτ x j hj v)).commutes c
/-- No two original analytic tangent directions produce the same
actual global candidate dual-number morphism. Surjectivity onto all
scheme tangents and algebraic smoothness remain separate questions. -/
theorem tangent_injective : Function.Injective (tangent τ hτ x j hj) := by
  intro v w h
  apply PELOriginalChartTangentInjection318.tangentDerivation_injective τ hτ x j hj
  apply EvaluationDualNumberLift318.lift_injective (algebraEvaluation τ hτ x j hj)
  have hc := (cancel_mono ((actualChartIso τ hτ j).hom ≫ (candidateChart τ hτ j).ι)).mp h
  have he := Spec.map_injective hc
  ext a
  exact congrArg (fun f : CommRingCat.of (CoordinateChart τ hτ j) ⟶
    CommRingCat.of Dual => f a) he
end PELOriginalCandidateSchemeTangent318
