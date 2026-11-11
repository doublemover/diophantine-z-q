module
public import PELOriginalCandidatePointEquivalence318
public import PELOriginalProjectiveCandidatePoints318
public section
noncomputable section
namespace PELOriginalProjectiveImageFromAffine318
open Set QuaternionicRealPeriod318 PELOriginalLevelTheta318 PELOriginalLevelPowerSections318
open PELOriginalCubicRelationIdeal318 PELOriginalAllLevelProjectiveMap318
open PELOriginalAllLevelHolomorphicMap318 PELOriginalChartAnalyticEvaluation318
open PELOriginalCandidateAffineOpenImage318 PELOriginalCandidatePointEquivalence318
open PELOriginalClosedAffineImage318 ComplexProjectiveQuotientTopology318
open ComplexProjectiveComplexAtlas318 ComplexProjectiveRatioCharts318
variable (τ : ℂ) (hτ : 0 < τ.im)

/-- The independent complex projective relation locus, defined by
nonzero homogeneous vectors satisfying ALL literal original relations.
This does not mention the theta image or a selected candidate open. -/
@[expose] def projectiveLocus : Set (Target 1) :=
  {p | ∃ v : Label 3 → ℂ, ∃ hv : v ≠ 0,
    Projectivization.mk ℂ v hv = p ∧
      ∀ F ∈ relations τ hτ, MvPolynomial.eval v F = 0}

lemma vector_chart_mem (v : Label 3 → ℂ) (hv : v ≠ 0)
    (hrel : ∀ F ∈ relations τ hτ, MvPolynomial.eval v F = 0)
    (j : Label 3) (hj : v j ≠ 0) :
    localChart (Label 3) 0 j (Projectivization.mk ℂ v hv) ∈ candidateLocus τ hτ j := by
  let f := PELOriginalCandidateVectorEvaluation318.evaluation τ hτ j v hrel hj
  have he : localChart (Label 3) 0 j (Projectivization.mk ℂ v hv) =
      pointVector τ hτ j f := by
    change coordinates (Label 3) 0 j (toAffine (Label 3) j (Projectivization.mk ℂ v hv)) = _
    have hr : toAffine (Label 3) j (Projectivization.mk ℂ v hv) =
        (fun i => f (ratioElement τ hτ j i.val)) := by
      funext i
      rw [toAffine,normalized_mk]
      exact (PELOriginalCandidateVectorEvaluation318.evaluation_ratio τ hτ j v hrel hj i.val).symm
    rw [hr]
    rfl
  rw [he]
  exact pointVector_mem τ hτ j f

lemma original_image_subset : PELOriginalLevelThreeClosedEmbedding318.image τ hτ ⊆
    projectiveLocus τ hτ := by
  rintro p ⟨q,rfl⟩
  exact ⟨baseVector τ hτ 1 q,baseVector_nonzero τ hτ 1 q,rfl,
    relation_evaluation τ hτ q⟩

/-- Whole affine image equality on every actual coordinate chart
implies equality of the ENTIRE independent projective relation locus
with the genuine original projective image. This helper does not supply
its affine hypothesis; the actual normalization boundary theorem does. -/
theorem equality_of_affine
    (hfull : ∀ j : Label 3, candidateLocus τ hτ j ⊆ affineImage τ hτ j) :
    projectiveLocus τ hτ = PELOriginalLevelThreeClosedEmbedding318.image τ hτ := by
  apply Set.Subset.antisymm
  · rintro p ⟨v,hv,rfl,hrel⟩
    have hn : ∃ j : Label 3, v j ≠ 0 := by
      by_contra h
      push_neg at h
      exact hv (funext h)
    obtain ⟨j,hj⟩ := hn
    let c := localChart (Label 3) 0 j
    have hp : Projectivization.mk ℂ v hv ∈ c.source :=
      (mk_mem_domain (Label 3) j v hv).mpr hj
    have ha := hfull j (vector_chart_mem τ hτ v hv hrel j hj)
    rw [affineImage_eq_preimage] at ha
    change c.symm (c (Projectivization.mk ℂ v hv)) ∈
      PELOriginalLevelThreeClosedEmbedding318.image τ hτ at ha
    rwa [c.left_inv hp] at ha
  · exact original_image_subset τ hτ
end PELOriginalProjectiveImageFromAffine318
