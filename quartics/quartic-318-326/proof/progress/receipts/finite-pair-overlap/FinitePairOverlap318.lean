module
public import BranchFullOverlap318
public section
noncomputable section
namespace FinitePairOverlap318
open CategoryTheory AlgebraicGeometry Polynomial
open ContactOverlapMaps318 BranchFullOverlap318
set_option maxHeartbeats 800000
set_option synthInstance.maxSize 256
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (c:Fin 4→ℚˣ)
local instance originalOpen : IsOpenImmersion (ContactProjectiveModel318.sourceOpen c):=
  ContactProjectiveModel318.sourceOpen_open c
local instance sourceAlgebra : Algebra (Whole c) (Source c):=(SourceOpenFractionField318.orderToOpen c).toAlgebra
local instance sourceLocalization : IsLocalization.Away (SourceOpenFractionField318.d c) (Source c):=
  SourceOpenFractionField318.open_isLocalization c

lemma basicOpen_coefficient (i:Fin 4):
    PrimeSpectrum.basicOpen (algebraMap ℚ[X] (Whole c) (ContactKummerOrder318.coefficient c i))=
      PrimeSpectrum.basicOpen (algebraMap ℚ[X] (Whole c) (X-C (LinearContactSquareclass318.contacts i))):=by
  change PrimeSpectrum.basicOpen (algebraMap ℚ[X] (Whole c)
    (C (c i:ℚ)*(X-C (LinearContactSquareclass318.contacts i))))=_
  rw [map_mul,PrimeSpectrum.basicOpen_mul]
  have h:algebraMap ℚ[X] (Whole c) (C (c i:ℚ))=algebraMap ℚ (Whole c) (c i:ℚ):=by
    exact (IsScalarTower.algebraMap_apply ℚ ℚ[X] (Whole c) (c i:ℚ)).symm
  rw [h,ContactFullOverlap318.basicOpen_unit _ ((c i).isUnit.map (algebraMap ℚ (Whole c))),top_inf_eq]

@[expose] def contactOpen (i:Fin 4):TopologicalSpace.Opens (PrimeSpectrum (Whole c)):=
  PrimeSpectrum.basicOpen (algebraMap ℚ[X] (Whole c) (X-C (LinearContactSquareclass318.contacts i)))

lemma denominator_open (i:Fin 4):
    PrimeSpectrum.basicOpen (SourceDenominatorCover318.denominator c i)=
    contactOpen c (FourRootPivot318.indices i 1)⊓
      (contactOpen c (FourRootPivot318.indices i 2)⊓contactOpen c (FourRootPivot318.indices i 3)):=by
  change PrimeSpectrum.basicOpen (algebraMap ℚ[X] (Whole c)
    (∏j:Fin 3,ContactKummerOrder318.coefficient c (FourRootPivot318.indices i j.succ)))=_
  simp only [Fin.prod_univ_succ,Fin.prod_univ_zero,map_mul,map_one,mul_one,PrimeSpectrum.basicOpen_mul,basicOpen_coefficient]
  rfl

lemma full_denominator_open :
    PrimeSpectrum.basicOpen (SourceOpenFractionField318.d c)=
      contactOpen c 0⊓(contactOpen c 1⊓(contactOpen c 2⊓contactOpen c 3)):=by
  change PrimeSpectrum.basicOpen (algebraMap ℚ[X] (Whole c)
    (∏i:Fin 4,(X-C (LinearContactSquareclass318.contacts i))))=_
  simp only [Fin.prod_univ_succ,Fin.prod_univ_zero,map_mul,map_one,mul_one,PrimeSpectrum.basicOpen_mul]
  rfl

lemma four_inf_pair {α:Type*} [SemilatticeInf α] (a:Fin 4→α) (i j:Fin 4) (hij:i≠j):
    (a (FourRootPivot318.indices i 1)⊓(a (FourRootPivot318.indices i 2)⊓a (FourRootPivot318.indices i 3)))⊓
    (a (FourRootPivot318.indices j 1)⊓(a (FourRootPivot318.indices j 2)⊓a (FourRootPivot318.indices j 3)))=
    a 0⊓(a 1⊓(a 2⊓a 3)):=by
  fin_cases i <;> fin_cases j <;> try contradiction
  all_goals simp [FourRootPivot318.indices,inf_assoc,inf_left_comm,inf_comm]

/-- The two different three-other-contact denominators together invert
all four contacts, including all allowed points and every pair of indices. -/
theorem basicOpen_intersection (i j:Fin 4) (hij:i≠j):
    PrimeSpectrum.basicOpen (SourceDenominatorCover318.denominator c i)⊓
      PrimeSpectrum.basicOpen (SourceDenominatorCover318.denominator c j)=
    PrimeSpectrum.basicOpen (SourceOpenFractionField318.d c):=by
  rw [denominator_open,denominator_open,full_denominator_open]
  exact four_inf_pair (contactOpen c) i j hij

lemma image_inf {X Y:Scheme} (f:X⟶Y) [IsOpenImmersion f] (U V:X.Opens):
    f ''ᵁ(U⊓V)=(f ''ᵁ U)⊓(f ''ᵁ V):=by
  apply TopologicalSpace.Opens.ext
  exact Set.image_inter f.isOpenEmbedding.injective

@[expose] def branchToWhole (i:Fin 4):Spec (CommRingCat.of (Branch c i))⟶Spec (CommRingCat.of (Whole c)):=
  Spec.map (CommRingCat.ofHom (algebraMap (Whole c) (Branch c i)))
instance branchToWhole_open (i:Fin 4):IsOpenImmersion (branchToWhole c i):=
  IsOpenImmersion.of_isLocalization (SourceDenominatorCover318.denominator c i)

theorem branchToWhole_range (i:Fin 4):(branchToWhole c i).opensRange=
    PrimeSpectrum.basicOpen (SourceDenominatorCover318.denominator c i):=by
  apply TopologicalSpace.Opens.ext
  exact PrimeSpectrum.localization_away_comap_range (Branch c i) (SourceDenominatorCover318.denominator c i)

theorem sourceInclusion_range :(sourceInclusion c).opensRange=
    PrimeSpectrum.basicOpen (SourceOpenFractionField318.d c):=by
  apply TopologicalSpace.Opens.ext
  exact PrimeSpectrum.localization_away_comap_range (Source c) (SourceOpenFractionField318.d c)

/-- Exact full image intersection of every pair of distinct actual finite
branch charts in the original global normalization. -/
theorem actual_full_intersection (i j:Fin 4) (hij:i≠j):
    (ContactIntrinsicFrames318.branchEmbedding c i).opensRange⊓
      (ContactIntrinsicFrames318.branchEmbedding c j).opensRange=
    (ContactProjectiveModel318.sourceOpen c).opensRange:=by
  change (branchToWhole c i≫SourceGlobalAffine318.chartEmbedding c).opensRange⊓
    (branchToWhole c j≫SourceGlobalAffine318.chartEmbedding c).opensRange=_
  rw [Scheme.Hom.opensRange_comp,Scheme.Hom.opensRange_comp,←image_inf,
    branchToWhole_range,branchToWhole_range,basicOpen_intersection c i j hij,
    ←sourceInclusion_range,←Scheme.Hom.opensRange_comp]
  simp only [ContactOverlapMaps318.source_square]

theorem maps_agree (i j:Fin 4):
    branchInclusion c i≫ContactIntrinsicFrames318.branchEmbedding c i=
      branchInclusion c j≫ContactIntrinsicFrames318.branchEmbedding c j:=by
  rw [branch_square,branch_square]

theorem actual_pullback (i j:Fin 4) (hij:i≠j):
    IsPullback (branchInclusion c i) (branchInclusion c j)
      (ContactIntrinsicFrames318.branchEmbedding c i) (ContactIntrinsicFrames318.branchEmbedding c j):=by
  apply IsOpenImmersion.isPullback
  · exact (maps_agree c i j).symm
  · have h:ContactIntrinsicFrames318.branchEmbedding c j ''ᵁ
        (ContactIntrinsicFrames318.branchEmbedding c j⁻¹ᵁ(ContactIntrinsicFrames318.branchEmbedding c i).opensRange)=
      ContactIntrinsicFrames318.branchEmbedding c j ''ᵁ(branchInclusion c j).opensRange:=by
      rw [Scheme.Hom.image_preimage_eq_opensRange_inf,inf_comm,actual_full_intersection c i j hij,
        ←Scheme.Hom.opensRange_comp]
      simp only [branch_square]
    apply le_antisymm
    · exact (Scheme.Hom.image_le_image_iff _ _ _).mp h.le
    · exact (Scheme.Hom.image_le_image_iff _ _ _).mp h.ge
end FinitePairOverlap318
