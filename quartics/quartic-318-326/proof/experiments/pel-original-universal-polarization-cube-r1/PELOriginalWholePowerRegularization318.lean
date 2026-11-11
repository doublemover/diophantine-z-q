module
public import PELOriginalWholePowerRegular318
public import PELOriginalChartPointSeparation318
public section
noncomputable section
namespace PELOriginalWholePowerRegularization318
open QuaternionicRealPeriod318
open PELOriginalLevelTheta318 PELOriginalLevelPowerSections318
open PELOriginalCandidateAffineCharts318 PELOriginalChartAnalyticEvaluation318
open PELOriginalCandidatePointEquivalence318 PELOriginalWholePowerChartRatios318
open PELOriginalSectionMultiplication318 PELOriginalWholePowerRatioCover318
open PELOriginalSexticRatioCover318 (theta_lift)
variable (τ : ℂ) (hτ : 0 < τ.im) (m : ℕ) (j : Label 3)

/-- The unique WHOLE chart section realizing the actual degree3m ratio. -/
@[expose] def element (s : homogeneous τ hτ (3*m)) : CoordinateChart τ hτ j :=
  Classical.choose (PELOriginalWholePowerRegular318.every_section τ hτ m j s)

lemma evaluation (s : homogeneous τ hτ (3*m)) (f : CoordinateChart τ hτ j →ₐ[ℂ] ℂ) :
    f (element τ hτ m j s)=candidateRatio τ hτ m j s (toLocus τ hτ j f) :=
  Classical.choose_spec (PELOriginalWholePowerRegular318.every_section τ hτ m j s) f

lemma unique (s : homogeneous τ hτ (3*m)) (a : CoordinateChart τ hτ j)
    (ha : ∀ f : CoordinateChart τ hτ j →ₐ[ℂ] ℂ,
      f a=candidateRatio τ hτ m j s (toLocus τ hτ j f)) : a=element τ hτ m j s := by
  apply PELOriginalChartPointSeparation318.ext τ hτ j
  intro f
  exact (ha f).trans (evaluation τ hτ m j s f).symm

/-- Actual regularization is C-linear on the FULL original H0(3m), not
only on a chosen theta span. Uniqueness removes every choice of
normalization, primitive element, denominator and polynomial numerator. -/
@[expose] def linear : homogeneous τ hτ (3*m) →ₗ[ℂ] CoordinateChart τ hτ j where
  toFun := element τ hτ m j
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

lemma cover_evaluation (s : homogeneous τ hτ (3*m)) (z : ComplexVectors)
    (hz : value τ hτ 3 j z ≠ 0) :
    algebraEvaluation τ hτ z j hz (linear τ hτ m j s)=coverRatio τ hτ m j s z := by
  obtain ⟨a,ha⟩ := PELOriginalWholePowerRegular318.every_section_on_cover τ hτ m j s
  have he : a=element τ hτ m j s := by
    apply PELOriginalChartPointSeparation318.ext τ hτ j
    intro f
    obtain ⟨w,hw,rfl⟩ := PELOriginalFullCandidatePoints318.every_chart_point τ hτ j f
    have h := evaluation τ hτ m j s (algebraEvaluation τ hτ w j hw)
    have hp := PELOriginalFullCandidatePoints318.pointVector_original τ hτ j w hw
    have hl : toLocus τ hτ j (algebraEvaluation τ hτ w j hw)=
        (⟨PELOriginalAllLevelHolomorphicMap318.ratioVector τ hτ 1 j w,
          PELOriginalFullCandidatePoints318.original_subset_candidate τ hτ j ⟨w,hw,rfl⟩⟩ : Locus τ hτ j) :=
      Subtype.ext hp
    rw [hl,candidate_original] at h
    exact (ha w hw).trans h.symm
  change algebraEvaluation τ hτ z j hz (element τ hτ m j s)=_
  rw [←he]
  exact ha z hz

@[expose] def theta [NeZero (3*m)] (r : Label (3*m)) : CoordinateChart τ hτ j :=
  linear τ hτ m j (thetaVector τ hτ (3*m) r)

lemma theta_evaluation [NeZero (3*m)] (r : Label (3*m)) (z : ComplexVectors)
    (hz : value τ hτ 3 j z ≠ 0) :
    algebraEvaluation τ hτ z j hz (theta τ hτ m j r)=
      value τ hτ (3*m) r z/(value τ hτ 3 j z)^m := by
  simpa only [theta,coverRatio,theta_lift] using
    cover_evaluation τ hτ m j (thetaVector τ hτ (3*m) r) z hz
end PELOriginalWholePowerRegularization318
