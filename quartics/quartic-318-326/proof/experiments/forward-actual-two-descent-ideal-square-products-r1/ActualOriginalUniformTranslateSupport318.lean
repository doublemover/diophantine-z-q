module
public import ActualOriginalFourierTiling318
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Analysis.Normed.Group.Uniform
public section
noncomputable section
namespace ActualOriginalUniformTranslateSupport318
open QuadricCRTAssembly318 ActualOriginalIntegerTiling318 Set Topology
set_option maxHeartbeats 16000000

lemma actual_integer_embedding_closed : IsClosedEmbedding integerEmbed :=
  (Real.isClosedEmbedding_intCast.prodMap Real.isClosedEmbedding_intCast).prodMap
    ((Real.isClosedEmbedding_intCast.prodMap Real.isClosedEmbedding_intCast).prodMap
      Real.isClosedEmbedding_intCast)

/-- Every compact source region meets only finitely many integer
translates of the SAME compact support. This is uniform over the compact
region, not merely a pointwise finite-support assertion. -/
theorem actual_uniform_translate_support (f : Coordinates ℝ → ℂ)
    (hf : HasCompactSupport f) {K : Set (Coordinates ℝ)} (hK : IsCompact K) :
    ∃ s : Finset (Coordinates ℤ), ∀ x ∈ K, ∀ z ∉ s, f (integerEmbed z+x)=0 := by
  classical
  let A : Set (Coordinates ℤ) := integerEmbed ⁻¹'
    ((fun p : Coordinates ℝ × Coordinates ℝ => p.1-p.2) '' (tsupport f ×ˢ K))
  have hA : A.Finite :=
    (actual_integer_embedding_closed.isCompact_preimage
      ((hf.prod hK).image (continuous_fst.sub continuous_snd))).finite
  refine ⟨hA.toFinset,fun x hx z hz => ?_⟩
  by_contra hnonzero
  apply hz
  rw [hA.mem_toFinset]
  exact ⟨(integerEmbed z+x,x),⟨subset_tsupport f hnonzero,hx⟩,by simp⟩

end ActualOriginalUniformTranslateSupport318
