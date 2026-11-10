module
public import OriginalChartZeroKernelIso318
public import AffineCartierKernelRegular318
public section
noncomputable section
namespace OriginalCartierZeroKernelIso318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace LineSheafClass318
open OriginalJointAffineFrameBasis318 SectionZeroAffineRefinement318 AffineCartierKernelRegular318
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {X Z : Scheme.{u}} (L : Line X) (s : Γ(L.object,⊤))
  {κ : Type u} (A : κ → CommRingCat.{u}) (j : ∀ a,Spec (A a) ⟶ X)
  [∀ a,IsOpenImmersion (j a)] (hc : ⊤≤⨆a,(j a).opensRange)
  (p : Z ⟶ X) [QuasiCompact p]
  (z : ∀ a,Spec (CommRingCat.of (A a⧸sectionIdeal (A a) (j a) L s)) ⟶ Z)
  (hz : ∀ a,IsPullback (Spec.map (CommRingCat.ofHom
    (Ideal.Quotient.mk (sectionIdeal (A a) (j a) L s)))) (z a) (j a) p)
  (hp : OriginalRegularClosedCharts318.Property p)
local notation "F" => InverseLineSectionContraction318.hom L s
local notation "G" => ActualClosedIdealModule318.structure p

/-- The joint original affine/frame/chart basis refined by ACTUAL
nonzerodivisors in the same zero kernel. Existence is proved below from
the original scheme-theoretic Cartier charts. -/
abbrev Index := {b : OriginalJointAffineFrameBasis318.Index L A j // HasRegularKernel p (U L A j b)}
abbrev openSet (b : Index L A j p) := U L A j b.val

lemma basis : Opens.IsBasis (Set.range (openSet L A j p)) := by
  apply Opens.isBasis_iff_nbhd.mpr
  intro V x hx
  obtain ⟨i,hi⟩ := Opens.mem_iSup.mp (L.cover (show x∈(⊤:X.Opens) from trivial))
  obtain ⟨a,ha⟩ := Opens.mem_iSup.mp (hc (show x∈(⊤:X.Opens) from trivial))
  obtain ⟨C,k,hk,hxk,d,q,hq,hd⟩ := hp x
  haveI : IsOpenImmersion k := hk
  obtain ⟨W,hW,hxW,hWV⟩ := exists_isAffineOpen_mem_and_subset
    (show x∈V⊓(L.opens i⊓((j a).opensRange⊓k.opensRange)) from ⟨hx,hi,ha,hxk⟩)
  let b : OriginalJointAffineFrameBasis318.Index L A j :=
    ⟨⟨W,hW⟩,i,a,hWV.trans (inf_le_right.trans inf_le_left),
      hWV.trans (inf_le_right.trans (inf_le_right.trans inf_le_left))⟩
  have hsub : (⟨W,hW⟩ : X.affineOpens)≤AffineQuotientKernelSections318.chartOpen C k := by
    change W≤k ''ᵁ ⊤
    rw [Scheme.Hom.image_top_eq_opensRange]
    exact hWV.trans (inf_le_right.trans (inf_le_right.trans inf_le_right))
  have hreg : HasRegularKernel p W := on_affine_subopen p C k d q hq hd ⟨W,hW⟩ hsub
  exact ⟨W,⟨⟨b,hreg⟩,rfl⟩,hxW,hWV.trans inf_le_left⟩

lemma image_basis : Opens.IsBasis (Set.range (fun b : Index L A j p =>
    embedding L A j b.val ''ᵁ ⊤)) := by
  have he : (fun b : Index L A j p => embedding L A j b.val ''ᵁ ⊤)=openSet L A j p := by
    funext b
    exact OriginalJointAffineFrameBasis318.image L A j b.val
  rw [he]
  exact basis L A j hc p hp

lemma injective_on_basis (b : Index L A j p) :
    Function.Injective (F.app (embedding L A j b.val ''ᵁ ⊤)) := by
  have hg := b.property
  rw [← OriginalJointAffineFrameBasis318.image L A j b.val] at hg
  obtain ⟨d,hd,hreg⟩ := hg
  have hm : d∈LinearMap.range (F.val.app (op (embedding L A j b.val ''ᵁ ⊤))).hom := by
    rw [OriginalChartZeroKernelIso318.exact_on_basis L s A j p z hz b.val,
      ActualClosedIdealModule318.section_kernel]
    exact hd
  rw [InverseLineSectionContraction318.range_on_subopen L s b.val.frame
    (embedding L A j b.val ''ᵁ ⊤) (OriginalJointAffineFrameBasis318.frame_le L A j b.val)] at hm
  apply InverseLineSectionContraction318.injective_on_subopen L s b.val.frame
    (embedding L A j b.val ''ᵁ ⊤) (OriginalJointAffineFrameBasis318.frame_le L A j b.val)
  exact regular_of_mem_principal _ d hreg hm

/-- The regularity premise of the earlier global comparison is now
DISCHARGED from genuine Cartier charts of the same original zero map.
The refined basis, kernel nonzerodivisors, exact contraction image and
injectivity are all constructed; no specialized-section claim is made. -/
@[expose] def iso : (FramedLineInverse318.inverse L).object ≅ ActualClosedIdealModule318.object p :=
  ModuleBasisKernel318.iso F G
    (fun b : Index L A j p => embedding L A j b.val ''ᵁ ⊤)
    (image_basis L A j hc p hp)
    (fun b => OriginalChartZeroKernelIso318.exact_on_basis L s A j p z hz b.val)
    (injective_on_basis L s A j p z hz)

@[reassoc] lemma iso_inclusion : (iso L s A j hc p z hz hp).hom ≫
    ActualClosedIdealModule318.inclusion p=F :=
  ModuleBasisKernel318.iso_hom_inclusion F G
    (fun b : Index L A j p => embedding L A j b.val ''ᵁ ⊤)
    (image_basis L A j hc p hp)
    (fun b => OriginalChartZeroKernelIso318.exact_on_basis L s A j p z hz b.val)
    (injective_on_basis L s A j p z hz)
end OriginalCartierZeroKernelIso318
