module
public import PELOriginalCandidateChartBase318
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public section
noncomputable section
namespace PELOriginalDerivativeOpenCharts318
open AlgebraicGeometry CategoryTheory
open PELOriginalLevelTheta318 PELOriginalCandidateAffineCharts318
open PELOriginalCandidateNineChartCover318
variable (τ : ℂ) (hτ : 0 < τ.im) (j : Label 3)

/-- Actual whole principal open inside the SAME original projective
candidate, with its original coordinate chart and structure morphism. -/
@[expose] def inclusion (d : CoordinateChart τ hτ j) :
    Spec (CommRingCat.of (Localization.Away d)) ⟶
      PELOriginalReducedProjectiveCandidate318.candidate τ hτ :=
  Spec.map (CommRingCat.ofHom (algebraMap (CoordinateChart τ hτ j) _)) ≫ chartMap τ hτ j

lemma open_immersion (d : CoordinateChart τ hτ j) :
    IsOpenImmersion (inclusion τ hτ j d) := by
  letI : IsOpenImmersion (Spec.map (CommRingCat.ofHom
      (algebraMap (CoordinateChart τ hτ j) (Localization.Away d)))) :=
    IsOpenImmersion.of_isLocalization d
  change IsOpenImmersion (_ ≫ chartMap τ hτ j)
  infer_instance

@[reassoc] lemma original_complex_base (d : CoordinateChart τ hτ j) :
    inclusion τ hτ j d ≫ PELOriginalProperComplexCandidate318.structureMap τ hτ =
      Spec.map (CommRingCat.ofHom (algebraMap ℂ (Localization.Away d))) := by
  rw [inclusion,Category.assoc,PELOriginalCandidateChartBase318.chart_over_complex_base,
    ←Spec.map_comp]
  congr 1
  ext c
  exact (IsScalarTower.algebraMap_apply ℂ (CoordinateChart τ hτ j) _ c).symm
end PELOriginalDerivativeOpenCharts318
