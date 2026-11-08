module
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.IsIso
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public section
noncomputable section
namespace EtaleSectionTrivialization318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable {E S : Scheme} (p : E ⟶ S) [Etale p]
variable {I : Type} (s : I → (S ⟶ E)) (hs : ∀ i, s i ≫ p = 𝟙 S)
include p hs in
/-- Each actual section is an open immersion, by the actual etale diagonal. -/
theorem section_open (i : I) : IsOpenImmersion (s i) := by
  have hP : MorphismProperty.HasOfPostcompProperty (@IsOpenImmersion) (@Etale) := by
    apply MorphismProperty.hasOfPostcompProperty_iff_le_diagonal.mpr
    intro X Y f hf
    letI : Etale f := hf
    exact inferInstanceAs (IsOpenImmersion (pullback.diagonal f))
  have hi : IsOpenImmersion (s i ≫ p) := by rw [hs i]; infer_instance
  exact hP.of_postcomp (s i) p inferInstance hi

variable (F : Type) [Field F] [IsAlgClosed F] (b : Spec (CommRingCat.of F) ⟶ S)
/-- Evaluation of the original section over one actual geometric base point. -/
@[expose] def value (i : I) : {t : Spec (CommRingCat.of F) ⟶ E // t ≫ p = b} :=
  ⟨b ≫ s i,by rw [Category.assoc,hs i,Category.comp_id]⟩
variable {F}
/-- The geometric test is a bijection of actual maps, not just underlying points. -/
@[expose] def GeometricBijective : Prop := ∀ (F : Type) [Field F] [IsAlgClosed F]
    (b : Spec (CommRingCat.of F) ⟶ S), Function.Bijective (value p s hs F b)

variable (h : GeometricBijective p s hs)
include h in
lemma disjoint : Pairwise (fun i j => Disjoint (Set.range (s i)) (Set.range (s j))) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  rintro _ ⟨x,hx⟩ ⟨y,hy⟩
  obtain ⟨z,_,_⟩ := Scheme.Pullback.exists_preimage_pullback x y (hx.trans hy.symm)
  let F := AlgebraicClosure ((pullback (s i) (s j)).residueField z)
  let t : Spec (CommRingCat.of F) ⟶ pullback (s i) (s j) :=
    Spec.map (CommRingCat.ofHom (algebraMap ((pullback (s i) (s j)).residueField z) F)) ≫
      (pullback (s i) (s j)).fromSpecResidueField z
  let b := t ≫ pullback.fst (s i) (s j)
  have hc : b ≫ s i = (t ≫ pullback.snd (s i) (s j)) ≫ s j := by
    dsimp only [b]
    rw [Category.assoc,pullback.condition,←Category.assoc]
  have hb : b = t ≫ pullback.snd (s i) (s j) := by
    have he := congrArg (fun f => f ≫ p) hc
    simpa only [Category.assoc,hs,Category.comp_id] using he
  have he : value p s hs F b i = value p s hs F b j := by
    apply Subtype.ext
    change b ≫ s i = b ≫ s j
    exact hc.trans (congrArg (fun f => f ≫ s j) hb.symm)
  exact hij ((h F b).injective he)

include h in
lemma covers : (⋃ i, Set.range (s i)) = Set.univ := by
  apply Set.eq_univ_iff_forall.mpr
  intro y
  let F := AlgebraicClosure (E.residueField y)
  let t : Spec (CommRingCat.of F) ⟶ E :=
    Spec.map (CommRingCat.ofHom (algebraMap (E.residueField y) F)) ≫ E.fromSpecResidueField y
  obtain ⟨i,hi⟩ := (h F (t ≫ p)).surjective ⟨t,rfl⟩
  have he : (t ≫ p) ≫ s i = t := congrArg Subtype.val hi
  apply Set.mem_iUnion.mpr
  refine ⟨i,⟨(t ≫ p) (IsLocalRing.closedPoint F),?_⟩⟩
  have hh := congrArg (fun f => f (IsLocalRing.closedPoint F)) he
  exact hh.trans (Scheme.fromSpecResidueField_apply y _)

include h in
/-- The actual disjoint union of the section domains is isomorphic to E.
The proof uses open immersions and actual map tests, preserving nilpotents. -/
theorem isIso : IsIso (Sigma.desc s) := by
  letI : ∀ i, IsOpenImmersion (s i) := section_open p s hs
  haveI : IsOpenImmersion (Sigma.desc s) := isOpenImmersion_sigmaDesc (fun _ : I => S) s (disjoint p s hs h)
  haveI : Surjective (Sigma.desc s) := Surjective.sigmaDesc_of_union_range_eq_univ (covers p s hs h)
  exact (isIso_iff_isOpenImmersion_and_surjective _).mpr ⟨inferInstance,inferInstance⟩

@[expose] def iso : (∐ fun _ : I => S) ≅ E := by
  letI := isIso p s hs h
  exact asIso (Sigma.desc s)
@[reassoc] theorem component (i : I) : Sigma.ι (fun _ : I => S) i ≫ (iso p s hs h).hom = s i :=
  Sigma.ι_comp_desc s i
@[reassoc] theorem base : (iso p s hs h).hom ≫ p = Sigma.desc (fun _ : I => 𝟙 S) := by
  apply Sigma.hom_ext
  intro i
  rw [component_assoc,hs i,Sigma.ι_comp_desc]
end EtaleSectionTrivialization318
