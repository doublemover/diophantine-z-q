module
public import PELOriginalCandidateVectorEvaluation318
public import PELOriginalClosedAffineImage318
public section
noncomputable section
namespace PELOriginalCandidateAffineOpenImage318
open Set QuaternionicRealPeriod318 PELOriginalLevelTheta318 PELOriginalLevelPowerSections318
open PELOriginalCandidateAffineCharts318 PELOriginalCubicRelationIdeal318
open PELOriginalChartAnalyticEvaluation318 PELOriginalProjectedFiniteOpen318
open PELOriginalAllLevelHolomorphicMap318 PELOriginalFullLocalizedPoints318
open PELOriginalCandidateVectorEvaluation318
open ComplexProjectiveComplexAtlas318 ComplexProjectiveRatioCharts318
variable (τ : ℂ) (hτ : 0 < τ.im) (j : Label 3)

/-- Literal normalized homogeneous coordinates of the independent
ambient affine point, using the original project's fixed chart model. -/
@[expose] def homogeneousVector (w : TargetModel 1) : Label 3 → ℂ :=
  embed (Label 3) j ((coordinates (Label 3) 0 j).symm w)

lemma homogeneousVector_at (w : TargetModel 1) : homogeneousVector j w j = 1 := by
  simp [homogeneousVector,embed]

/-- The candidate affine zero locus defined by ALL actual homogeneous
relations, independently of the theta image or monogenic root model. -/
@[expose] def candidateLocus : Set (TargetModel 1) :=
  {w | ∀ p ∈ relations τ hτ, MvPolynomial.eval (homogeneousVector j w) p = 0}

lemma normalized_ratios (w : TargetModel 1) :
    coordinates (Label 3) 0 j
      (fun i : {i : Label 3 // i ≠ j} =>
        homogeneousVector j w i.val / homogeneousVector j w j) = w := by
  have he : (fun i : {i : Label 3 // i ≠ j} =>
      homogeneousVector j w i.val / homogeneousVector j w j) =
      (coordinates (Label 3) 0 j).symm w := by
    funext i
    simp only [homogeneousVector_at,div_one,homogeneousVector,embed,dif_neg i.property]
  rw [he,LinearEquiv.apply_symm_apply]

/-- The SAME produced principal-open condition on an independent
candidate point. It is evaluated in the entire actual chart ring. -/
@[expose] def candidateOpen (x : ComplexVectors) (d : BasePolynomial) : Set (TargetModel 1) :=
  {w | ∃ hw : w ∈ candidateLocus τ hτ j,
    evaluation τ hτ j (homogeneousVector j w) hw
      (by rw [homogeneousVector_at]; exact one_ne_zero)
      (polynomialMap τ hτ j x d) ≠ 0}

/-- Every independent ambient candidate point on the produced open
is literally an original affine theta-image point, with all coordinates
in the fixed original ambient model unchanged. -/
theorem exists_candidate_open_image (x : ComplexVectors)
    (hx : value τ hτ 3 j x ≠ 0) :
    ∃ d : BasePolynomial, d ≠ 0 ∧ polynomialMap τ hτ j x d ≠ 0 ∧
      candidateOpen τ hτ j x d ⊆ PELOriginalClosedAffineImage318.affineImage τ hτ j := by
  obtain ⟨d,hd,ha,hfull⟩ := exists_full_chart_open τ hτ j x hx
  refine ⟨d,hd,ha,?_⟩
  rintro w ⟨hw,hdw⟩
  let f := evaluation τ hτ j (homogeneousVector j w) hw
    (by rw [homogeneousVector_at]; exact one_ne_zero)
  obtain ⟨z,hz⟩ := hfull f hdw
  refine ⟨z.val,z.property.1,?_⟩
  have hr : (fun i : {i : Label 3 // i ≠ j} =>
      value τ hτ 3 i.val z.val / value τ hτ 3 j z.val) =
      (fun i : {i : Label 3 // i ≠ j} =>
        homogeneousVector j w i.val / homogeneousVector j w j) := by
    funext i
    have hi := hz (ratioElement τ hτ j i.val)
    rw [actual_ratio_evaluation] at hi
    exact hi.symm.trans (evaluation_ratio τ hτ j (homogeneousVector j w) hw _ i.val)
  rw [ratioVector,hr,normalized_ratios]
end PELOriginalCandidateAffineOpenImage318
