module
public import ContactFullOverlap318
public import BranchOverlapLocalization318
public import ContactIntrinsicFrames318
public section
noncomputable section
namespace BranchFullOverlap318
open CategoryTheory AlgebraicGeometry ContactOverlapMaps318
set_option maxHeartbeats 800000
set_option synthInstance.maxSize 256
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (c:Fin 4→ℚˣ)
local instance originalOpen : IsOpenImmersion (ContactProjectiveModel318.sourceOpen c):=
  ContactProjectiveModel318.sourceOpen_open c
abbrev Branch (i:Fin 4):=BranchOverlapLocalization318.Branch c i
local instance branchAlgebra (i:Fin 4):Algebra (Branch c i) (Source c):=(BranchOverlapLocalization318.toOpen c i).toAlgebra
local instance branchLocalization (i:Fin 4):IsLocalization.Away
    (algebraMap (Whole c) (Branch c i) (BranchOverlapLocalization318.factor c i)) (Source c):=
  BranchOverlapLocalization318.whole_localization c i

@[expose] def branchInclusion (i:Fin 4):ContactKummerCover318.cover c⟶Spec (CommRingCat.of (Branch c i)):=
  Spec.map (CommRingCat.ofHom (BranchOverlapLocalization318.toOpen c i))
instance branchInclusion_open (i:Fin 4):IsOpenImmersion (branchInclusion c i):=
  IsOpenImmersion.of_isLocalization
    (algebraMap (Whole c) (Branch c i) (BranchOverlapLocalization318.factor c i))

theorem branch_square (i:Fin 4):branchInclusion c i≫ContactIntrinsicFrames318.branchEmbedding c i=
    ContactProjectiveModel318.sourceOpen c:=by
  have h:CommRingCat.ofHom (algebraMap (Whole c) (Branch c i))≫
      CommRingCat.ofHom (BranchOverlapLocalization318.toOpen c i)=
      CommRingCat.ofHom (SourceOpenFractionField318.orderToOpen c):=by
    apply CommRingCat.hom_ext
    exact RingHom.ext (BranchOverlapLocalization318.toOpen_on_source c i)
  unfold branchInclusion ContactIntrinsicFrames318.branchEmbedding
  rw [←Category.assoc,←Spec.map_comp,h]
  exact source_square c

lemma branch_range_le_source (i:Fin 4):
    (ContactIntrinsicFrames318.branchEmbedding c i).opensRange≤(SourceGlobalAffine318.chartEmbedding c).opensRange:=by
  unfold ContactIntrinsicFrames318.branchEmbedding
  rw [Scheme.Hom.opensRange_comp]
  exact Scheme.Hom.image_le_opensRange _ _

lemma original_range_le_branch (i:Fin 4):
    (ContactProjectiveModel318.sourceOpen c).opensRange≤(ContactIntrinsicFrames318.branchEmbedding c i).opensRange:=by
  have h:(branchInclusion c i≫ContactIntrinsicFrames318.branchEmbedding c i).opensRange≤
      (ContactIntrinsicFrames318.branchEmbedding c i).opensRange:=by
    rw [Scheme.Hom.opensRange_comp]
    exact Scheme.Hom.image_le_opensRange _ _
  simpa only [branch_square] using h

/-- Every finite-branch/infinity intersection is the same entire original
unbranched source, universally over all four actual branch charts. -/
theorem actual_full_intersection (i:Fin 4):
    (ContactIntrinsicFrames318.branchEmbedding c i).opensRange⊓
      (InfinityGlobalScheme318.chartEmbedding c).opensRange=
    (ContactProjectiveModel318.sourceOpen c).opensRange:=by
  apply le_antisymm
  · exact (inf_le_inf (branch_range_le_source c i) le_rfl).trans
      (ContactFullOverlap318.actual_full_intersection c).le
  · apply le_inf (original_range_le_branch c i)
    have h:(infinityInclusion c≫InfinityGlobalScheme318.chartEmbedding c).opensRange≤
        (InfinityGlobalScheme318.chartEmbedding c).opensRange:=by
      rw [Scheme.Hom.opensRange_comp]
      exact Scheme.Hom.image_le_opensRange _ _
    simpa only [infinity_square] using h

/-- Literal commutativity for the branch and infinity restrictions used by
the intrinsic differential sheaf; both sides are the original sourceOpen. -/
theorem maps_agree (i:Fin 4):
    branchInclusion c i≫ContactIntrinsicFrames318.branchEmbedding c i=
      infinityInclusion c≫InfinityGlobalScheme318.chartEmbedding c:=by
  rw [branch_square,infinity_square]
/-- Each of the four actual finite-branch/infinity squares is cartesian on
the whole stated open, with the same unbranched source and explicit maps. -/
theorem actual_pullback (i:Fin 4):IsPullback (branchInclusion c i) (infinityInclusion c)
    (ContactIntrinsicFrames318.branchEmbedding c i) (InfinityGlobalScheme318.chartEmbedding c):=by
  apply IsOpenImmersion.isPullback
  · exact (maps_agree c i).symm
  · have h:InfinityGlobalScheme318.chartEmbedding c ''ᵁ
        (InfinityGlobalScheme318.chartEmbedding c⁻¹ᵁ(ContactIntrinsicFrames318.branchEmbedding c i).opensRange)=
      InfinityGlobalScheme318.chartEmbedding c ''ᵁ(infinityInclusion c).opensRange:=by
      rw [Scheme.Hom.image_preimage_eq_opensRange_inf,inf_comm,actual_full_intersection,
        ←Scheme.Hom.opensRange_comp]
      simp only [infinity_square]
    apply le_antisymm
    · exact (Scheme.Hom.image_le_image_iff _ _ _).mp h.le
    · exact (Scheme.Hom.image_le_image_iff _ _ _).mp h.ge
end BranchFullOverlap318
