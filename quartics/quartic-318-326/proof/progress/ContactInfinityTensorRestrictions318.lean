module
public import ContactFiniteTensorRestrictions318
public section
noncomputable section
namespace ContactInfinityTensorRestrictions318
open AlgebraicGeometry CategoryTheory Opposite
open ContactOverlapIntrinsic318 ContactFiniteOverlapDifferential318
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable (c : Fin 4 → ℚˣ)
local instance infinityMap_open :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom (ContactOverlapAlgebraMaps318.infinityMap c).toRingHom)) :=
  ContactOverlapMaps318.infinityInclusion_open c

lemma infinityLE : embedding c ''ᵁ ⊤ ≤ InfinityGlobalScheme318.chartEmbedding c ''ᵁ ⊤ := by
  have h : (ContactOverlapMaps318.infinityInclusion c ≫ InfinityGlobalScheme318.chartEmbedding c).opensRange≤
      (InfinityGlobalScheme318.chartEmbedding c).opensRange := by
    rw [Scheme.Hom.opensRange_comp]
    exact Scheme.Hom.image_le_opensRange _ _
  simpa only [Scheme.Hom.image_top_eq_opensRange,embedding,ContactOverlapMaps318.infinity_square] using h

theorem q0_restrict :
    (ContactDirectTensorSections318.tensor c).presheaf.map (homOfLE (infinityLE c)).op
      (ContactDirectTensorSections318.infinityQ0 c)=ContactCommonTensorSections318.infinityQ0 c := by
  have h2 := IntrinsicTensorChartSections318.weightedSquare_restrict_to
    (R:=ℚ) (S:=InfinityGlobalChart318.InfinityOrder c) (T:=O c)
    (InfinityGlobalScheme318.chartEmbedding c)
    (ContactIntrinsicDifferentials318.structureMap c) (InfinityStructureSmooth318.chartEmbedding_over_Q c)
    (ContactOverlapAlgebraMaps318.infinityMap c)
    (embedding c) (over_Q c) (ContactOverlapMaps318.infinity_square c) (infinityLE c)
    (ContactBicanonicalCoefficients318.infinityQ0 c)
    (KaehlerDifferential.D ℚ (InfinityGlobalChart318.InfinityOrder c)
      (ContactFrameNormalization318.infinityCoordinate c))
  have h3 := congrArg (IntrinsicTensorChartSections318.weightedSquare (R:=ℚ) (S:=O c)
    (embedding c) (ContactIntrinsicDifferentials318.structureMap c) (over_Q c)
    (ContactOverlapAlgebraMaps318.infinityMap c (ContactBicanonicalCoefficients318.infinityQ0 c)))
    (AlgHomDifferential318.map_D (ContactOverlapAlgebraMaps318.infinityMap c)
      (ContactFrameNormalization318.infinityCoordinate c))
  exact h2.trans h3

theorem q0_common (i : Fin 4) :
    (ContactDirectTensorSections318.tensor c).presheaf.map
      (homOfLE (ContactFiniteTensorRestrictions318.branchLE c i)).op
      (ContactDirectTensorSections318.branchQ0 c i)=
    (ContactDirectTensorSections318.tensor c).presheaf.map (homOfLE (infinityLE c)).op
      (ContactDirectTensorSections318.infinityQ0 c) :=
  (ContactFiniteTensorRestrictions318.q0_restrict c i).trans
    ((ContactCommonTensorSections318.finite_infinity_q0 c i).trans (q0_restrict c).symm)

/-- Exact compatibility over the full actual branch/infinity intersection. -/
theorem q0_branch_infinity (i : Fin 4) :
    LocalSectionCompatibility318.Agree (ContactDirectTensorSections318.tensor c)
      (ContactIntrinsicFrames318.branchEmbedding c i ''ᵁ ⊤)
      (InfinityGlobalScheme318.chartEmbedding c ''ᵁ ⊤)
      (ContactDirectTensorSections318.branchQ0 c i)
      (ContactDirectTensorSections318.infinityQ0 c) := by
  let P (V : (ContactGlobalSmooth318.Model c).Opens) :=
    ∀ (hVi : V ≤ ContactIntrinsicFrames318.branchEmbedding c i ''ᵁ ⊤)
      (hVn : V ≤ InfinityGlobalScheme318.chartEmbedding c ''ᵁ ⊤),
    (ContactDirectTensorSections318.tensor c).presheaf.map (homOfLE hVi).op
      (ContactDirectTensorSections318.branchQ0 c i)=
    (ContactDirectTensorSections318.tensor c).presheaf.map (homOfLE hVn).op
      (ContactDirectTensorSections318.infinityQ0 c)
  have hc : P (embedding c ''ᵁ ⊤) := fun _ _ => q0_common c i
  have hi : embedding c ''ᵁ ⊤ =
      (ContactIntrinsicFrames318.branchEmbedding c i ''ᵁ ⊤) ⊓
        (InfinityGlobalScheme318.chartEmbedding c ''ᵁ ⊤) := by
    simpa only [Scheme.Hom.image_top_eq_opensRange,embedding] using
      (BranchFullOverlap318.actual_full_intersection c i).symm
  exact (Eq.mp (congrArg P hi) hc) inf_le_left inf_le_right
theorem q1_restrict :
    (ContactDirectTensorSections318.tensor c).presheaf.map (homOfLE (infinityLE c)).op
      (ContactDirectTensorSections318.infinityQ1 c)=ContactCommonTensorSections318.infinityQ1 c := by
  have h2 := IntrinsicTensorChartSections318.weightedSquare_restrict_to
    (R:=ℚ) (S:=InfinityGlobalChart318.InfinityOrder c) (T:=O c)
    (InfinityGlobalScheme318.chartEmbedding c)
    (ContactIntrinsicDifferentials318.structureMap c) (InfinityStructureSmooth318.chartEmbedding_over_Q c)
    (ContactOverlapAlgebraMaps318.infinityMap c)
    (embedding c) (over_Q c) (ContactOverlapMaps318.infinity_square c) (infinityLE c)
    (ContactBicanonicalCoefficients318.infinityQ1 c)
    (KaehlerDifferential.D ℚ (InfinityGlobalChart318.InfinityOrder c)
      (ContactFrameNormalization318.infinityCoordinate c))
  have h3 := congrArg (IntrinsicTensorChartSections318.weightedSquare (R:=ℚ) (S:=O c)
    (embedding c) (ContactIntrinsicDifferentials318.structureMap c) (over_Q c)
    (ContactOverlapAlgebraMaps318.infinityMap c (ContactBicanonicalCoefficients318.infinityQ1 c)))
    (AlgHomDifferential318.map_D (ContactOverlapAlgebraMaps318.infinityMap c)
      (ContactFrameNormalization318.infinityCoordinate c))
  exact h2.trans h3

theorem q1_common (i : Fin 4) :
    (ContactDirectTensorSections318.tensor c).presheaf.map
      (homOfLE (ContactFiniteTensorRestrictions318.branchLE c i)).op
      (ContactDirectTensorSections318.branchQ1 c i)=
    (ContactDirectTensorSections318.tensor c).presheaf.map (homOfLE (infinityLE c)).op
      (ContactDirectTensorSections318.infinityQ1 c) :=
  (ContactFiniteTensorRestrictions318.q1_restrict c i).trans
    ((ContactCommonTensorSections318.finite_infinity_q1 c i).trans (q1_restrict c).symm)

/-- Exact compatibility over the full actual branch/infinity intersection. -/
theorem q1_branch_infinity (i : Fin 4) :
    LocalSectionCompatibility318.Agree (ContactDirectTensorSections318.tensor c)
      (ContactIntrinsicFrames318.branchEmbedding c i ''ᵁ ⊤)
      (InfinityGlobalScheme318.chartEmbedding c ''ᵁ ⊤)
      (ContactDirectTensorSections318.branchQ1 c i)
      (ContactDirectTensorSections318.infinityQ1 c) := by
  let P (V : (ContactGlobalSmooth318.Model c).Opens) :=
    ∀ (hVi : V ≤ ContactIntrinsicFrames318.branchEmbedding c i ''ᵁ ⊤)
      (hVn : V ≤ InfinityGlobalScheme318.chartEmbedding c ''ᵁ ⊤),
    (ContactDirectTensorSections318.tensor c).presheaf.map (homOfLE hVi).op
      (ContactDirectTensorSections318.branchQ1 c i)=
    (ContactDirectTensorSections318.tensor c).presheaf.map (homOfLE hVn).op
      (ContactDirectTensorSections318.infinityQ1 c)
  have hc : P (embedding c ''ᵁ ⊤) := fun _ _ => q1_common c i
  have hi : embedding c ''ᵁ ⊤ =
      (ContactIntrinsicFrames318.branchEmbedding c i ''ᵁ ⊤) ⊓
        (InfinityGlobalScheme318.chartEmbedding c ''ᵁ ⊤) := by
    simpa only [Scheme.Hom.image_top_eq_opensRange,embedding] using
      (BranchFullOverlap318.actual_full_intersection c i).symm
  exact (Eq.mp (congrArg P hi) hc) inf_le_left inf_le_right
end ContactInfinityTensorRestrictions318
