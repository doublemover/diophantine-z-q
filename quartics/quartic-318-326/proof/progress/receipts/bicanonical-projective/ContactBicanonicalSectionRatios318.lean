module
public import ContactBicanonicalRatios318
public import ContactBicanonicalGenerators318
public section
noncomputable section
namespace ContactBicanonicalSectionRatios318
open AlgebraicGeometry CategoryTheory Opposite
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable (c : Fin 4 → ℚˣ)

@[expose] def branchRatioSection (i : Fin 4) :
    Γ(ContactGlobalSmooth318.Model c,ContactIntrinsicFrames318.branchEmbedding c i ''ᵁ ⊤) :=
  ((ContactIntrinsicFrames318.branchEmbedding c i).appIso ⊤).inv
    ((Scheme.ΓSpecIso (CommRingCat.of (ContactIntrinsicFrames318.BranchRing c i))).inv
      (ContactBicanonicalRatios318.branchRatio c i))
@[expose] def infinityRatioSection :
    Γ(ContactGlobalSmooth318.Model c,InfinityGlobalScheme318.chartEmbedding c ''ᵁ ⊤) :=
  ((InfinityGlobalScheme318.chartEmbedding c).appIso ⊤).inv
    ((Scheme.ΓSpecIso (CommRingCat.of (InfinityGlobalChart318.InfinityOrder c))).inv
      (ContactBicanonicalRatios318.infinityRatio c))

theorem branch_relation (i : Fin 4) :
    ContactDirectTensorSections318.branchQ1 c i=
      branchRatioSection c i • ContactDirectTensorSections318.branchQ0 c i := by
  unfold ContactDirectTensorSections318.branchQ1 ContactDirectTensorSections318.branchQ0
    branchRatioSection
  rw [ContactBicanonicalRatios318.branchRatio_eq]
  exact IntrinsicTensorChartSections318.weightedSquare_mul _ _ _ _ _ _

theorem infinity_relation :
    ContactDirectTensorSections318.infinityQ0 c=
      infinityRatioSection c • ContactDirectTensorSections318.infinityQ1 c := by
  unfold ContactDirectTensorSections318.infinityQ0 ContactDirectTensorSections318.infinityQ1
    infinityRatioSection
  rw [ContactBicanonicalRatios318.infinityRatio_eq,
    ContactBicanonicalRatios318.infinity_coefficient_relation]
  exact IntrinsicTensorChartSections318.weightedSquare_mul _ _ _ _ _ _

/-- This ratio is characterized by the actual global sections, not merely by
an unrelated coefficient formula. -/
theorem global_branch_relation (i : Fin 4) :
    (ContactGlobalBicanonical318.tensor c).presheaf.map (homOfLE (show
      (ContactIntrinsicFrames318.branchEmbedding c i ''ᵁ ⊤) ≤ ⊤ from le_top)).op
      (ContactGlobalBicanonical318.q1 c)=
    branchRatioSection c i •
      (ContactGlobalBicanonical318.tensor c).presheaf.map (homOfLE (show
        (ContactIntrinsicFrames318.branchEmbedding c i ''ᵁ ⊤) ≤ ⊤ from le_top)).op
        (ContactGlobalBicanonical318.q0 c) := by
  exact (ContactGlobalBicanonical318.q1_restrict c (some i)).trans
    ((branch_relation c i).trans (congrArg (fun s => branchRatioSection c i • s)
      (ContactGlobalBicanonical318.q0_restrict c (some i)).symm))

theorem global_infinity_relation :
    (ContactGlobalBicanonical318.tensor c).presheaf.map (homOfLE (show
      (InfinityGlobalScheme318.chartEmbedding c ''ᵁ ⊤) ≤ ⊤ from le_top)).op
      (ContactGlobalBicanonical318.q0 c)=
    infinityRatioSection c •
      (ContactGlobalBicanonical318.tensor c).presheaf.map (homOfLE (show
        (InfinityGlobalScheme318.chartEmbedding c ''ᵁ ⊤) ≤ ⊤ from le_top)).op
        (ContactGlobalBicanonical318.q1 c) := by
  exact (ContactGlobalBicanonical318.q0_restrict c none).trans
    ((infinity_relation c).trans (congrArg (fun s => infinityRatioSection c • s)
      (ContactGlobalBicanonical318.q1_restrict c none).symm))

/-- Uniqueness of q1/q0 in the actual structure sheaf on the full finite chart. -/
theorem branch_ratio_unique (i : Fin 4)
    (a : Γ(ContactGlobalSmooth318.Model c,(ContactIntrinsicFrames318.branchEmbedding c i ''ᵁ ⊤)))
    (h : a • (ContactGlobalBicanonical318.tensor c).presheaf.map
      (homOfLE (show (ContactIntrinsicFrames318.branchEmbedding c i ''ᵁ ⊤) ≤ ⊤ from le_top)).op
      (ContactGlobalBicanonical318.q0 c)=
      (ContactGlobalBicanonical318.tensor c).presheaf.map
      (homOfLE (show (ContactIntrinsicFrames318.branchEmbedding c i ''ᵁ ⊤) ≤ ⊤ from le_top)).op
      (ContactGlobalBicanonical318.q1 c)) : a=branchRatioSection c i :=
  (ContactBicanonicalGenerators318.global_branch_generator c i _ le_rfl).1
    (h.trans (global_branch_relation c i))

/-- Uniqueness of q0/q1 on the full infinity chart, including u=0. -/
theorem infinity_ratio_unique
    (a : Γ(ContactGlobalSmooth318.Model c,(InfinityGlobalScheme318.chartEmbedding c ''ᵁ ⊤)))
    (h : a • (ContactGlobalBicanonical318.tensor c).presheaf.map
      (homOfLE (show (InfinityGlobalScheme318.chartEmbedding c ''ᵁ ⊤) ≤ ⊤ from le_top)).op
      (ContactGlobalBicanonical318.q1 c)=
      (ContactGlobalBicanonical318.tensor c).presheaf.map
      (homOfLE (show (InfinityGlobalScheme318.chartEmbedding c ''ᵁ ⊤) ≤ ⊤ from le_top)).op
      (ContactGlobalBicanonical318.q0 c)) : a=infinityRatioSection c :=
  (ContactBicanonicalGenerators318.global_infinity_generator c _ le_rfl).1
    (h.trans (global_infinity_relation c))
end ContactBicanonicalSectionRatios318
