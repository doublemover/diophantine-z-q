module
public import FramedAffineZeroKernel318
public import ModuleBasisKernel318
public section
noncomputable section
namespace OriginalJointAffineFrameBasis318
open AlgebraicGeometry CategoryTheory TopologicalSpace LineSheafClass318
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {X : Scheme.{u}} (L : Line X) {κ : Type u} (A : κ → CommRingCat.{u})
  (j : ∀ a,Spec (A a) ⟶ X) [∀ a,IsOpenImmersion (j a)]
  (hc : ⊤≤⨆a,(j a).opensRange)

/-- Joint ORIGINAL affine/frame/chart refinements, with actual containing
indices retained so subsequent maps cannot silently switch source charts. -/
structure Index where
  affine : X.affineOpens
  frame : L.Index
  chart : κ
  frame_le : affine.1≤L.opens frame
  chart_le : affine.1≤(j chart).opensRange

abbrev U (b : Index L A j) := b.affine.1
abbrev ring (b : Index L A j) := Γ(X,b.affine.1)

include hc in
/-- All small affine neighborhoods in original frame/chart intersections
form a basis, not just a point-surjective list of unrelated charts. -/
lemma basis : Opens.IsBasis (Set.range (U L A j)) := by
  apply Opens.isBasis_iff_nbhd.mpr
  intro V x hx
  obtain ⟨i,hi⟩ := Opens.mem_iSup.mp (L.cover (show x∈(⊤:X.Opens) from trivial))
  obtain ⟨a,ha⟩ := Opens.mem_iSup.mp (hc (show x∈(⊤:X.Opens) from trivial))
  obtain ⟨W,hW,hxW,hWV⟩ := exists_isAffineOpen_mem_and_subset
    (show x∈V⊓(L.opens i⊓(j a).opensRange) from ⟨hx,hi,ha⟩)
  let b : Index L A j := ⟨⟨W,hW⟩,i,a,hWV.trans (inf_le_right.trans inf_le_left),
    hWV.trans (inf_le_right.trans inf_le_right)⟩
  exact ⟨W,⟨b,rfl⟩,hxW,hWV.trans inf_le_left⟩

lemma range_in_chart (b : Index L A j) :
    Set.range b.affine.2.fromSpec ⊆ Set.range (j b.chart) := by
  rw [b.affine.2.range_fromSpec]
  exact b.chart_le

/-- Actual lift of the affine-open embedding through its specified
original chart. Uniqueness is provided by the original open immersion. -/
@[expose] def lift (b : Index L A j) : Spec (ring L A j b) ⟶ Spec (A b.chart) :=
  IsOpenImmersion.lift (j b.chart) b.affine.2.fromSpec (range_in_chart L A j b)
lemma lift_fac (b : Index L A j) : lift L A j b ≫ j b.chart=b.affine.2.fromSpec :=
  IsOpenImmersion.lift_fac _ _ _

@[expose] def ringMap (b : Index L A j) : A b.chart ⟶ ring L A j b :=
  (Scheme.Spec.preimage (lift L A j b)).unop
lemma spec_ringMap (b : Index L A j) : Spec.map (ringMap L A j b)=lift L A j b :=
  Scheme.Spec.image_preimage _

@[expose] def embedding (b : Index L A j) : Spec (ring L A j b) ⟶ X :=
  Spec.map (ringMap L A j b) ≫ j b.chart
lemma embedding_eq (b : Index L A j) : embedding L A j b=b.affine.2.fromSpec := by
  rw [embedding,spec_ringMap,lift_fac]
instance embedding_open (b : Index L A j) : IsOpenImmersion (embedding L A j b) := by
  rw [embedding_eq]
  infer_instance
lemma image (b : Index L A j) : embedding L A j b ''ᵁ ⊤=U L A j b := by
  rw [Scheme.Hom.image_top_eq_opensRange,embedding_eq]
  apply TopologicalSpace.Opens.ext
  exact b.affine.2.range_fromSpec
lemma frame_le (b : Index L A j) : embedding L A j b ''ᵁ ⊤≤L.opens b.frame := by
  rw [image]
  exact b.frame_le

include hc in
/-- Same basis expressed as images of the actual affine Spec refinement
maps used by the section-zero quotient construction. -/
lemma image_basis : Opens.IsBasis (Set.range (fun b : Index L A j => embedding L A j b ''ᵁ ⊤)) := by
  have he : (fun b : Index L A j => embedding L A j b ''ᵁ ⊤)=U L A j := by
    funext b
    exact image L A j b
  rw [he]
  exact basis L A j hc
end OriginalJointAffineFrameBasis318
