module
public import ContactCommonTensorSections318
public import ContactDirectTensorSections318
public import FinitePairOverlap318
public import LocalSectionCompatibility318
public section
noncomputable section
namespace ContactFiniteTensorRestrictions318
open AlgebraicGeometry CategoryTheory Opposite
open ContactOverlapIntrinsic318 ContactFiniteOverlapDifferential318 ContactCommonTensorSections318
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable (c : Fin 4 → ℚˣ)
local instance branchMap_open (i : Fin 4) :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom (ContactOverlapAlgebraMaps318.branchMap c i).toRingHom)) :=
  BranchFullOverlap318.branchInclusion_open c i

lemma branchLE (i : Fin 4) : embedding c ''ᵁ ⊤ ≤ ContactIntrinsicFrames318.branchEmbedding c i ''ᵁ ⊤ := by
  simpa only [Scheme.Hom.image_top_eq_opensRange,embedding] using
    BranchFullOverlap318.original_range_le_branch c i

theorem q0_restrict (i : Fin 4) :
    (ContactDirectTensorSections318.tensor c).presheaf.map (homOfLE (branchLE c i)).op
      (ContactDirectTensorSections318.branchQ0 c i)=finiteQ0 c i := by
  have h2 := IntrinsicTensorChartSections318.weightedSquare_restrict_to
    (R:=ℚ) (S:=ContactIntrinsicFrames318.BranchRing c i) (T:=O c)
    (ContactIntrinsicFrames318.branchEmbedding c i)
    (ContactIntrinsicDifferentials318.structureMap c) (ContactIntrinsicFrames318.branch_structure c i)
    (ContactOverlapAlgebraMaps318.branchMap c i)
    (embedding c) (over_Q c) (BranchFullOverlap318.branch_square c i) (branchLE c i)
    (ContactBicanonicalCoefficients318.branchQ0 c i)
    (KaehlerDifferential.D ℚ (ContactIntrinsicFrames318.BranchRing c i)
      (ContactFrameNormalization318.sourceCoordinate c i))
  have h3 := congrArg (IntrinsicTensorChartSections318.weightedSquare (R:=ℚ) (S:=O c)
    (embedding c) (ContactIntrinsicDifferentials318.structureMap c) (over_Q c)
    (ContactOverlapAlgebraMaps318.branchMap c i (ContactBicanonicalCoefficients318.branchQ0 c i)))
    (AlgHomDifferential318.map_D (ContactOverlapAlgebraMaps318.branchMap c i)
      (ContactFrameNormalization318.sourceCoordinate c i))
  exact h2.trans h3

theorem q0_common (i j : Fin 4) :
    (ContactDirectTensorSections318.tensor c).presheaf.map (homOfLE (branchLE c i)).op
      (ContactDirectTensorSections318.branchQ0 c i)=
    (ContactDirectTensorSections318.tensor c).presheaf.map (homOfLE (branchLE c j)).op
      (ContactDirectTensorSections318.branchQ0 c j) :=
  (q0_restrict c i).trans ((finiteQ0_eq c i j).trans (q0_restrict c j).symm)

/-- Compatibility on the complete actual finite/finite chart intersection,
not a dense-open equality asserted to extend. -/
theorem q0_finite_pair (i j : Fin 4) (hij : i≠j) :
    LocalSectionCompatibility318.Agree (ContactDirectTensorSections318.tensor c)
      (ContactIntrinsicFrames318.branchEmbedding c i ''ᵁ ⊤)
      (ContactIntrinsicFrames318.branchEmbedding c j ''ᵁ ⊤)
      (ContactDirectTensorSections318.branchQ0 c i)
      (ContactDirectTensorSections318.branchQ0 c j) := by
  let P (V : (ContactGlobalSmooth318.Model c).Opens) :=
    ∀ (hVi : V ≤ ContactIntrinsicFrames318.branchEmbedding c i ''ᵁ ⊤)
      (hVj : V ≤ ContactIntrinsicFrames318.branchEmbedding c j ''ᵁ ⊤),
    (ContactDirectTensorSections318.tensor c).presheaf.map (homOfLE hVi).op
      (ContactDirectTensorSections318.branchQ0 c i)=
    (ContactDirectTensorSections318.tensor c).presheaf.map (homOfLE hVj).op
      (ContactDirectTensorSections318.branchQ0 c j)
  have hc : P (embedding c ''ᵁ ⊤) := fun _ _ => q0_common c i j
  have hi : embedding c ''ᵁ ⊤ =
      (ContactIntrinsicFrames318.branchEmbedding c i ''ᵁ ⊤) ⊓
        (ContactIntrinsicFrames318.branchEmbedding c j ''ᵁ ⊤) := by
    simpa only [Scheme.Hom.image_top_eq_opensRange,embedding] using
      (FinitePairOverlap318.actual_full_intersection c i j hij).symm
  exact (Eq.mp (congrArg P hi) hc) inf_le_left inf_le_right
theorem q1_restrict (i : Fin 4) :
    (ContactDirectTensorSections318.tensor c).presheaf.map (homOfLE (branchLE c i)).op
      (ContactDirectTensorSections318.branchQ1 c i)=finiteQ1 c i := by
  have h2 := IntrinsicTensorChartSections318.weightedSquare_restrict_to
    (R:=ℚ) (S:=ContactIntrinsicFrames318.BranchRing c i) (T:=O c)
    (ContactIntrinsicFrames318.branchEmbedding c i)
    (ContactIntrinsicDifferentials318.structureMap c) (ContactIntrinsicFrames318.branch_structure c i)
    (ContactOverlapAlgebraMaps318.branchMap c i)
    (embedding c) (over_Q c) (BranchFullOverlap318.branch_square c i) (branchLE c i)
    (ContactBicanonicalCoefficients318.branchQ1 c i)
    (KaehlerDifferential.D ℚ (ContactIntrinsicFrames318.BranchRing c i)
      (ContactFrameNormalization318.sourceCoordinate c i))
  have h3 := congrArg (IntrinsicTensorChartSections318.weightedSquare (R:=ℚ) (S:=O c)
    (embedding c) (ContactIntrinsicDifferentials318.structureMap c) (over_Q c)
    (ContactOverlapAlgebraMaps318.branchMap c i (ContactBicanonicalCoefficients318.branchQ1 c i)))
    (AlgHomDifferential318.map_D (ContactOverlapAlgebraMaps318.branchMap c i)
      (ContactFrameNormalization318.sourceCoordinate c i))
  exact h2.trans h3

theorem q1_common (i j : Fin 4) :
    (ContactDirectTensorSections318.tensor c).presheaf.map (homOfLE (branchLE c i)).op
      (ContactDirectTensorSections318.branchQ1 c i)=
    (ContactDirectTensorSections318.tensor c).presheaf.map (homOfLE (branchLE c j)).op
      (ContactDirectTensorSections318.branchQ1 c j) :=
  (q1_restrict c i).trans ((finiteQ1_eq c i j).trans (q1_restrict c j).symm)

/-- Compatibility on the complete actual finite/finite chart intersection,
not a dense-open equality asserted to extend. -/
theorem q1_finite_pair (i j : Fin 4) (hij : i≠j) :
    LocalSectionCompatibility318.Agree (ContactDirectTensorSections318.tensor c)
      (ContactIntrinsicFrames318.branchEmbedding c i ''ᵁ ⊤)
      (ContactIntrinsicFrames318.branchEmbedding c j ''ᵁ ⊤)
      (ContactDirectTensorSections318.branchQ1 c i)
      (ContactDirectTensorSections318.branchQ1 c j) := by
  let P (V : (ContactGlobalSmooth318.Model c).Opens) :=
    ∀ (hVi : V ≤ ContactIntrinsicFrames318.branchEmbedding c i ''ᵁ ⊤)
      (hVj : V ≤ ContactIntrinsicFrames318.branchEmbedding c j ''ᵁ ⊤),
    (ContactDirectTensorSections318.tensor c).presheaf.map (homOfLE hVi).op
      (ContactDirectTensorSections318.branchQ1 c i)=
    (ContactDirectTensorSections318.tensor c).presheaf.map (homOfLE hVj).op
      (ContactDirectTensorSections318.branchQ1 c j)
  have hc : P (embedding c ''ᵁ ⊤) := fun _ _ => q1_common c i j
  have hi : embedding c ''ᵁ ⊤ =
      (ContactIntrinsicFrames318.branchEmbedding c i ''ᵁ ⊤) ⊓
        (ContactIntrinsicFrames318.branchEmbedding c j ''ᵁ ⊤) := by
    simpa only [Scheme.Hom.image_top_eq_opensRange,embedding] using
      (FinitePairOverlap318.actual_full_intersection c i j hij).symm
  exact (Eq.mp (congrArg P hi) hc) inf_le_left inf_le_right
end ContactFiniteTensorRestrictions318
