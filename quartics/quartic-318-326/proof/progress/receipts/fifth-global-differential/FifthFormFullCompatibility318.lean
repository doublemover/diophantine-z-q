module
public import FifthFormLocalSections318
public section
noncomputable section
namespace FifthFormFullCompatibility318
open AlgebraicGeometry CategoryTheory Opposite SourceTwistArithmetic318
open FifthFormLocalSections318 ContactOverlapIntrinsic318
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

theorem branch_common (i j:Fin 4):
    M.presheaf.map (homOfLE (ContactFiniteTensorRestrictions318.branchLE units i)).op (branch i)=
      M.presheaf.map (homOfLE (ContactFiniteTensorRestrictions318.branchLE units j)).op (branch j):=
  (branch_restrict i).trans ((FifthFormCommonOpen318.branch_eq_branch i j).trans (branch_restrict j).symm)

theorem infinity_common (j:Fin 4):
    M.presheaf.map (homOfLE (ContactFiniteTensorRestrictions318.branchLE units j)).op (branch j)=
      M.presheaf.map (homOfLE (ContactInfinityTensorRestrictions318.infinityLE units)).op infinity:=
  (branch_restrict j).trans (FifthFormCommonOpen318.branch_eq_infinity j |>.trans infinity_restrict.symm)

/-- Agreement holds on the complete actual finite/finite intersection. -/
theorem finite_pair (i j:Fin 4) (hij:i≠j):LocalSectionCompatibility318.Agree M
    (ContactIntrinsicFrames318.branchEmbedding units i ''ᵁ ⊤)
    (ContactIntrinsicFrames318.branchEmbedding units j ''ᵁ ⊤) (branch i) (branch j):=by
  let P (V:(ContactGlobalSmooth318.Model units).Opens):=
    ∀(hi:V≤ContactIntrinsicFrames318.branchEmbedding units i ''ᵁ ⊤)
      (hj:V≤ContactIntrinsicFrames318.branchEmbedding units j ''ᵁ ⊤),
        M.presheaf.map (homOfLE hi).op (branch i)=M.presheaf.map (homOfLE hj).op (branch j)
  have hc:P (embedding units ''ᵁ ⊤):=fun _ _=>branch_common i j
  have he:embedding units ''ᵁ ⊤=(ContactIntrinsicFrames318.branchEmbedding units i ''ᵁ ⊤)⊓
      (ContactIntrinsicFrames318.branchEmbedding units j ''ᵁ ⊤):=by
    simpa only [Scheme.Hom.image_top_eq_opensRange,embedding] using
      (FinitePairOverlap318.actual_full_intersection units i j hij).symm
  exact (Eq.mp (congrArg P he) hc) inf_le_left inf_le_right

/-- Agreement holds on the complete actual branch/infinity intersection. -/
theorem branch_infinity (j:Fin 4):LocalSectionCompatibility318.Agree M
    (ContactIntrinsicFrames318.branchEmbedding units j ''ᵁ ⊤)
    (InfinityGlobalScheme318.chartEmbedding units ''ᵁ ⊤) (branch j) infinity:=by
  let P (V:(ContactGlobalSmooth318.Model units).Opens):=
    ∀(hi:V≤ContactIntrinsicFrames318.branchEmbedding units j ''ᵁ ⊤)
      (hn:V≤InfinityGlobalScheme318.chartEmbedding units ''ᵁ ⊤),
        M.presheaf.map (homOfLE hi).op (branch j)=M.presheaf.map (homOfLE hn).op infinity
  have hc:P (embedding units ''ᵁ ⊤):=fun _ _=>infinity_common j
  have he:embedding units ''ᵁ ⊤=(ContactIntrinsicFrames318.branchEmbedding units j ''ᵁ ⊤)⊓
      (InfinityGlobalScheme318.chartEmbedding units ''ᵁ ⊤):=by
    simpa only [Scheme.Hom.image_top_eq_opensRange,embedding] using
      (BranchFullOverlap318.actual_full_intersection units j).symm
  exact (Eq.mp (congrArg P he) hc) inf_le_left inf_le_right
end FifthFormFullCompatibility318
