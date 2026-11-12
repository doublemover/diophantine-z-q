module
public import PELOriginalCandidateAffineTopology318
public import PELOriginalLevelThreeLocalImage318
public section
noncomputable section
namespace PELOriginalCandidateLocalGraph318
open Set QuaternionicRealPeriod318 DiscreteComplexPeriodAtlas318
open PELOriginalLevelTheta318 PELOriginalLevelPowerSections318
open PELOriginalPolarizationTransitions318 PELOriginalAllLevelProjectiveMap318
open PELOriginalAllLevelHolomorphicMap318 PELOriginalLevelThreeLocalImage318
open PELOriginalCandidatePointEquivalence318 PELOriginalCandidateAffineTopology318
open ComplexProjectiveQuotientTopology318
variable (τ : ℂ) (hτ : 0 < τ.im) (x : ComplexVectors) (j : Label 3)
  (hj : value τ hτ 3 j x ≠ 0)
local instance discretePeriods : DiscreteTopology (P τ) :=
  PELOriginalPeriodLattice318.original_discrete τ hτ
local instance targetTopology : TopologicalSpace (PELOriginalAllLevelHolomorphicMap318.Target 1) :=
  topology (Label 3)

/-- A genuine relatively OPEN neighborhood in the FULL candidate is an
actual holomorphic graph with continuous complex-linear inverse. The
neighborhood is proved open using the full independent candidate/source
homeomorphism, not declared open by transporting a manifold structure. -/
theorem exists_open_graph :
    ∃ W : Set ComplexVectors, IsOpen W ∧
      localProjection τ hτ x j (ratioVector τ hτ 1 j x) ∈ W ∧
      DifferentiableOn ℂ (imageGraph τ hτ x j hj) W ∧
      (∀ v ∈ W, localProjection τ hτ x j (imageGraph τ hτ x j hj v) = v) ∧
      (imageGraph τ hτ x j hj '' W ⊆
        PELOriginalCandidateAffineOpenImage318.candidateLocus τ hτ j) ∧
      IsOpen {w : Locus τ hτ j | w.val ∈ imageGraph τ hτ x j hj '' W} ∧
      ratioVector τ hτ 1 j x ∈ imageGraph τ hτ x j hj '' W := by
  obtain ⟨W,hW,hWx,hWt,hG,hsource,hproj,himage⟩ := local_holomorphic_image τ hτ x j hj
  let a := parameterChart τ hτ x j hj
  let t := PELOriginalPolarizationTransitions318.chart τ hτ x
  let D : Set ComplexVectors := a.source ∩ a ⁻¹' W
  have hD : IsOpen D := a.isOpen_inter_preimage hW
  have hDt : D ⊆ t.target := by
    intro z hz
    have hh := (hsource (a z) hz.2).1
    rwa [a.left_inv hz.1] at hh
  let U : Set (Base τ) := t.symm '' D
  have hU : IsOpen U := t.isOpen_image_symm_of_subset_target hD hDt
  let N : Set (Locus τ hτ j) := sourcePoint τ hτ j ⁻¹' U
  have hN : IsOpen N := hU.preimage (sourcePoint_continuous τ hτ j)
  have hsub : imageGraph τ hτ x j hj '' W ⊆
      PELOriginalCandidateAffineOpenImage318.candidateLocus τ hτ j := by
    rintro w ⟨v,hv,rfl⟩
    exact PELOriginalFullCandidatePoints318.original_subset_candidate τ hτ j
      ⟨a.symm v,(hsource v hv).2,rfl⟩
  have he : imageGraph τ hτ x j hj '' W = Subtype.val '' N := by
    apply Set.Subset.antisymm
    · rintro w ⟨v,hv,rfl⟩
      let z := a.symm v
      have hz : z ∈ D := ⟨a.map_target (hWt hv),by
        change a (a.symm v) ∈ W
        rwa [a.right_inv (hWt hv)]⟩
      let q : Locus τ hτ j := ⟨imageGraph τ hτ x j hj v,hsub ⟨v,hv,rfl⟩⟩
      refine ⟨q,?_,rfl⟩
      change sourcePoint τ hτ j q ∈ t.symm '' D
      refine ⟨z,hz,?_⟩
      have hq : sourcePoint τ hτ j q = DiscreteComplexPeriodAtlas318.projection (P τ) z :=
        sourcePoint_original τ hτ j z (hsource v hv).2
      simpa only [t,PELOriginalPolarizationTransitions318.chart,localChart_symm] using hq.symm
    · rintro w ⟨q,hq,rfl⟩
      obtain ⟨z,hz,hzq⟩ := hq
      have hh := actual_original_formula τ hτ x j z
      change ComplexProjectiveComplexAtlas318.localChart (Label 3) 0 j
        (projectiveMap τ hτ 1 (t.symm z)) = ratioVector τ hτ 1 j z at hh
      rw [hzq,sourcePoint_image,
        (ComplexProjectiveComplexAtlas318.localChart (Label 3) 0 j).right_inv (mem_univ q.val)] at hh
      rw [hh]
      rw [←himage]
      exact ⟨z,hz,rfl⟩
  have hopen : IsOpen {w : Locus τ hτ j | w.val ∈ imageGraph τ hτ x j hj '' W} := by
    have hset : {w : Locus τ hτ j | w.val ∈ imageGraph τ hτ x j hj '' W} = N := by
      rw [he]
      ext w
      constructor
      · rintro ⟨w',hw',heq⟩
        exact (Subtype.ext heq : w' = w) ▸ hw'
      · intro hw
        exact ⟨w,hw,rfl⟩
    rw [hset]
    exact hN
  refine ⟨W,hW,hWx,hG,hproj,hsub,hopen,?_⟩
  refine ⟨localProjection τ hτ x j (ratioVector τ hτ 1 j x),hWx,?_⟩
  exact SplitHolomorphicImage318.graph_center _ _ _ _
/-- Every point of the independent candidate has a genuine relatively
open two-complex-dimensional holomorphic graph chart, whose inverse is
an ambient complex-linear projection. The cover includes every boundary
point; this is a submanifold-chart assertion, not algebraic smoothness. -/
theorem every_candidate_open_graph (w : Locus τ hτ j) :
    ∃ W : Set ComplexVectors, ∃ G : ComplexVectors → TargetModel 1,
      ∃ p : TargetModel 1 →L[ℂ] ComplexVectors,
        IsOpen W ∧ DifferentiableOn ℂ G W ∧ (∀ v ∈ W, p (G v) = v) ∧
        (G '' W ⊆ PELOriginalCandidateAffineOpenImage318.candidateLocus τ hτ j) ∧
        IsOpen {q : Locus τ hτ j | q.val ∈ G '' W} ∧ w.val ∈ G '' W := by
  obtain ⟨z,hz,hcoord⟩ :=
    PELOriginalFullAffineCandidateImage318.full_candidate_subset_original τ hτ j w.property
  obtain ⟨W,hW,hcenter,hG,hproj,hsub,hopen,hmem⟩ := exists_open_graph τ hτ z j hz
  refine ⟨W,imageGraph τ hτ z j hz,localProjection τ hτ z j,
    hW,hG,hproj,hsub,hopen,?_⟩
  rwa [hcoord] at hmem
end PELOriginalCandidateLocalGraph318
