module
public import PELOriginalWholeSexticRegular318
public import PELOriginalChartPointSeparation318
public section
noncomputable section
namespace PELOriginalSexticRegularization318
open QuaternionicRealPeriod318
open PELOriginalLevelTheta318 PELOriginalLevelPowerSections318
open PELOriginalCandidateAffineCharts318 PELOriginalChartAnalyticEvaluation318
open PELOriginalCandidatePointEquivalence318 PELOriginalSexticChartRatios318
open PELOriginalSectionMultiplication318 PELOriginalSexticRatioCover318
variable (τ : ℂ) (hτ : 0 < τ.im) (j : Label 3)

/-- The unique WHOLE chart section realizing the actual sextic ratio. -/
@[expose] def element (s : homogeneous τ hτ 6) : CoordinateChart τ hτ j :=
  Classical.choose (PELOriginalWholeSexticRegular318.every_section τ hτ j s)

lemma evaluation (s : homogeneous τ hτ 6) (f : CoordinateChart τ hτ j →ₐ[ℂ] ℂ) :
    f (element τ hτ j s)=candidateRatio τ hτ j s (toLocus τ hτ j f) :=
  Classical.choose_spec (PELOriginalWholeSexticRegular318.every_section τ hτ j s) f

lemma unique (s : homogeneous τ hτ 6) (a : CoordinateChart τ hτ j)
    (ha : ∀ f : CoordinateChart τ hτ j →ₐ[ℂ] ℂ,
      f a=candidateRatio τ hτ j s (toLocus τ hτ j f)) : a=element τ hτ j s := by
  apply PELOriginalChartPointSeparation318.ext τ hτ j
  intro f
  exact (ha f).trans (evaluation τ hτ j s f).symm

/-- Actual regularization is C-linear on the FULL original H0(6), not
only on a chosen theta span. Uniqueness removes every choice of
normalization, primitive element, denominator and polynomial numerator. -/
@[expose] def linear : homogeneous τ hτ 6 →ₗ[ℂ] CoordinateChart τ hτ j where
  toFun := element τ hτ j
  map_add' s t := by
    apply PELOriginalChartPointSeparation318.ext τ hτ j
    intro f
    rw [map_add,evaluation,evaluation,evaluation]
    change (s.val _+t.val _)/_ = s.val _/_+t.val _/_
    exact add_div _ _ _
  map_smul' c s := by
    apply PELOriginalChartPointSeparation318.ext τ hτ j
    intro f
    rw [f.toLinearMap.map_smul,evaluation,evaluation]
    change (c*s.val _)/_ = c*(s.val _/_)
    exact mul_div_assoc _ _ _

lemma cover_evaluation (s : homogeneous τ hτ 6) (z : ComplexVectors)
    (hz : value τ hτ 3 j z ≠ 0) :
    algebraEvaluation τ hτ z j hz (linear τ hτ j s)=coverRatio τ hτ j s z := by
  obtain ⟨a,ha⟩ := PELOriginalWholeSexticRegular318.every_section_on_cover τ hτ j s
  have he : a=element τ hτ j s := by
    apply PELOriginalChartPointSeparation318.ext τ hτ j
    intro f
    obtain ⟨w,hw,rfl⟩ := PELOriginalFullCandidatePoints318.every_chart_point τ hτ j f
    have h := evaluation τ hτ j s (algebraEvaluation τ hτ w j hw)
    have hp := PELOriginalFullCandidatePoints318.pointVector_original τ hτ j w hw
    have hl : toLocus τ hτ j (algebraEvaluation τ hτ w j hw)=
        (⟨PELOriginalAllLevelHolomorphicMap318.ratioVector τ hτ 1 j w,
          PELOriginalFullCandidatePoints318.original_subset_candidate τ hτ j ⟨w,hw,rfl⟩⟩ : Locus τ hτ j) :=
      Subtype.ext hp
    rw [hl,candidate_original] at h
    exact (ha w hw).trans h.symm
  change algebraEvaluation τ hτ z j hz (element τ hτ j s)=_
  rw [←he]
  exact ha z hz

@[expose] def theta (r : Label 6) : CoordinateChart τ hτ j :=
  linear τ hτ j (thetaVector τ hτ 6 r)

lemma theta_evaluation (r : Label 6) (z : ComplexVectors)
    (hz : value τ hτ 3 j z ≠ 0) :
    algebraEvaluation τ hτ z j hz (theta τ hτ j r)=
      value τ hτ 6 r z/(value τ hτ 3 j z)^2 := by
  simpa only [theta,coverRatio,theta_lift] using
    cover_evaluation τ hτ j (thetaVector τ hτ 6 r) z hz
end PELOriginalSexticRegularization318
