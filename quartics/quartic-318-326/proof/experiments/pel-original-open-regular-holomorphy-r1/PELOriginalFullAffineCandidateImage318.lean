module
public import PELOriginalCandidateNormalizationTopology318
public section
noncomputable section
namespace PELOriginalFullAffineCandidateImage318
open Set QuaternionicRealPeriod318 PELOriginalLevelTheta318 PELOriginalLevelPowerSections318
open PELOriginalCandidateAffineCharts318 PELOriginalChartAnalyticEvaluation318
open PELOriginalCandidatePointEquivalence318 PELOriginalCandidateElementFunctions318
open PELOriginalCandidateAffineOpenImage318 PELOriginalCandidateNormalizationTopology318
open PELOriginalAllLevelHolomorphicMap318 PELOriginalClosedAffineImage318
open PELOriginalProjectedChartIndependence318
variable (τ : ℂ) (hτ : 0 < τ.im) (j : Label 3)

/-- The ENTIRE independently defined candidate affine zero locus is
contained in the genuine original theta image. The missing denominator
boundary is supplied by proved Euclidean normalization openness and a
produced nonzero base cutoff, not by Zariski-density terminology. -/
theorem candidate_subset_original (x : ComplexVectors) (hx : value τ hτ 3 j x ≠ 0) :
    candidateLocus τ hτ j ⊆ affineImage τ hτ j := by
  obtain ⟨n,g,hg,hf,d,hd,ha,b,hb,hfull⟩ :=
    PELOriginalNormalizationBaseCutoff318.exists_base_open_original_image τ hτ j x hx
  apply FiniteIntegralProjectionOpen318.subset_closed_of_base_cutoff
    (candidateLocus τ hτ j) (affineImage τ hτ j) (projection τ hτ j n g)
    (projection_open τ hτ j n g hg hf) (affineImage_closed τ hτ j) b hb
  intro w hw hbw
  let q : Locus τ hτ j := ⟨w,hw⟩
  let f := toPoint τ hτ j q
  let v : MvPolynomial (Fin n) ℂ →ₐ[ℂ] ℂ := MvPolynomial.aeval (projection τ hτ j n g w)
  obtain ⟨z,hz⟩ := hfull v f (projection_square τ hτ j n g q) hbw
  refine ⟨z.val,z.property.1,?_⟩
  funext i
  have hi := hz (coordinateElement τ hτ j i)
  rw [coordinate_evaluation] at hi
  exact hi.symm.trans (toPoint_coordinate τ hτ j q i)
/-- Unconditional full-chart inclusion for EVERY original coordinate
chart. Nonemptiness is produced from actual section independence. -/
theorem full_candidate_subset_original :
    candidateLocus τ hτ j ⊆ affineImage τ hτ j := by
  have hn := (original_values_independent τ hτ 3).ne_zero j
  have hex : ∃ x : ComplexVectors, value τ hτ 3 j x ≠ 0 := by
    by_contra h
    push_neg at h
    exact hn (funext h)
  obtain ⟨x,hx⟩ := hex
  exact candidate_subset_original τ hτ j x hx
end PELOriginalFullAffineCandidateImage318
