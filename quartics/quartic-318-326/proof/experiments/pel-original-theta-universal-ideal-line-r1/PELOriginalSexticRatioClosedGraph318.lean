module
public import PELOriginalSexticRatioCover318
public import PELOriginalCandidateElementFunctions318
public import Mathlib.Topology.Constructions.SumProd
public section
noncomputable section
namespace PELOriginalSexticRatioClosedGraph318
open Set Topology QuaternionicRealPeriod318 PELOriginalLevelTheta318 PELOriginalLevelPowerSections318
open PELOriginalSectionMultiplication318 PELOriginalCandidatePointEquivalence318
open PELOriginalCandidateAffineOpenImage318 PELOriginalAllLevelHolomorphicMap318
open PELOriginalSexticChartRatios318 PELOriginalSexticRatioCover318
variable (τ : ℂ) (hτ : 0 < τ.im) (j : Label 3) (s : homogeneous τ hτ 6)

/-- The graph over the ENTIRE independent affine candidate in the genuine
ambient coordinate space. It is not a graph restricted to a primitive open. -/
@[expose] def graph : Set (TargetModel 1 × ℂ) :=
  Set.range (fun w : Locus τ hτ j => (w.val,candidateRatio τ hτ j s w))

theorem graph_closed : IsClosed (graph τ hτ j s) := by
  have hc : IsClosed {p : Locus τ hτ j × ℂ | candidateRatio τ hτ j s p.1 = p.2} :=
    isClosed_eq ((candidateRatio_continuous τ hτ j s).comp continuous_fst) continuous_snd
  have he : IsClosedEmbedding
      (Prod.map (Subtype.val : Locus τ hτ j → TargetModel 1) (id : ℂ → ℂ)) :=
    (PELOriginalCandidateElementFunctions318.candidateLocus_closed τ hτ j).isClosedEmbedding_subtypeVal.prodMap
      (.id : IsClosedEmbedding (id : ℂ → ℂ))
  have himage : Prod.map (Subtype.val : Locus τ hτ j → TargetModel 1) (id : ℂ → ℂ) ''
      {p : Locus τ hτ j × ℂ | candidateRatio τ hτ j s p.1 = p.2} = graph τ hτ j s := by
    ext p
    constructor
    · rintro ⟨⟨w,z⟩,hw,rfl⟩
      exact ⟨w,Prod.ext rfl hw⟩
    · rintro ⟨w,rfl⟩
      exact ⟨(w,candidateRatio τ hτ j s w),rfl,rfl⟩
  rw [←himage]
  exact he.isClosedMap _ hc

/-- Exact equality with the original source graph, retaining the actual
whole-section recovered representative and all original chart points. -/
theorem graph_iff_original (p : TargetModel 1 × ℂ) :
    p ∈ graph τ hτ j s ↔ ∃ z : ComplexVectors, ∃ hz : value τ hτ 3 j z ≠ 0,
      (ratioVector τ hτ 1 j z,coverRatio τ hτ j s z) = p := by
  constructor
  · rintro ⟨w,rfl⟩
    obtain ⟨z,hz,hcoord⟩ :=
      PELOriginalFullAffineCandidateImage318.full_candidate_subset_original τ hτ j w.property
    let v : Locus τ hτ j := ⟨ratioVector τ hτ 1 j z,
      PELOriginalFullCandidatePoints318.original_subset_candidate τ hτ j ⟨z,hz,rfl⟩⟩
    have hv : v=w := Subtype.ext hcoord
    refine ⟨z,hz,Prod.ext hcoord ?_⟩
    have h := candidate_original τ hτ j s z hz
    change candidateRatio τ hτ j s v = coverRatio τ hτ j s z at h
    rw [hv] at h
    exact h.symm
  · rintro ⟨z,hz,rfl⟩
    refine ⟨⟨ratioVector τ hτ 1 j z,
      PELOriginalFullCandidatePoints318.original_subset_candidate τ hτ j ⟨z,hz,rfl⟩⟩,?_⟩
    exact Prod.ext rfl (candidate_original τ hτ j s z hz)

/-- Every candidate coordinate has exactly one value on this graph.
This will distinguish a true extra field extension from repeated original
points when applying whole-root exhaustion to the joint equation. -/
theorem graph_value_unique (v : TargetModel 1) (a b : ℂ)
    (ha : (v,a) ∈ graph τ hτ j s) (hb : (v,b) ∈ graph τ hτ j s) : a=b := by
  obtain ⟨w,hw⟩ := ha
  obtain ⟨w',hw'⟩ := hb
  have he : w=w' := Subtype.ext ((congrArg Prod.fst hw).trans (congrArg Prod.fst hw').symm)
  have h := congrArg Prod.snd hw
  have h' := congrArg Prod.snd hw'
  rw [he] at h
  exact h.symm.trans h'
end PELOriginalSexticRatioClosedGraph318
