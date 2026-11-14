module
public import OriginalUniversalPrincipalRegular318
public import AffineQuotientPullback318
public section
noncomputable section
namespace OriginalRegularIdealCover318
open AlgebraicGeometry CategoryTheory
universe u

/-- An ideal has genuine open affine charts whose extended ideals are
principal non-zero-divisors. Rings may be nonreduced; no radicals occur. -/
@[expose] def Property (A : CommRingCat.{u}) (I : Ideal A) : Prop :=
  ∀ x : Spec A, ∃ (B : CommRingCat.{u}) (f : A ⟶ B),
    IsOpenImmersion (Spec.map f) ∧ x ∈ Set.range (Spec.map f) ∧
    ∃ c : B, Ideal.map f.hom I=Ideal.span {c} ∧ ∀ b : B, b*c=0 → b=0

lemma equivalence {A D : CommRingCat.{u}} (e : A ≃+* D) (I : Ideal A) (J : Ideal D)
    (hJ : J=Ideal.map e.toRingHom I) (h : Property A I) : Property D J := by
  intro x
  obtain ⟨B,f,hf,⟨y,hy⟩,c,hc,hr⟩ := h (Spec.map (CommRingCat.ofHom e.toRingHom) x)
  let g : D ⟶ B := CommRingCat.ofHom e.symm.toRingHom ≫ f
  have hg : Spec.map g = Spec.map f ≫ Spec.map (CommRingCat.ofHom e.symm.toRingHom) :=
    Spec.map_comp _ _
  haveI : IsOpenImmersion (Spec.map f) := hf
  haveI : IsOpenImmersion (Spec.map (CommRingCat.ofHom e.symm.toRingHom)) := by
    change IsOpenImmersion (Scheme.Spec.mapIso e.symm.toCommRingCatIso.op).hom
    infer_instance
  have hopen : IsOpenImmersion (Spec.map g) := by rw [hg]; infer_instance
  have hid : Spec.map (CommRingCat.ofHom e.toRingHom) ≫
      Spec.map (CommRingCat.ofHom e.symm.toRingHom)=𝟙 (Spec D) := by
    rw [← Spec.map_comp]
    have hh : CommRingCat.ofHom e.symm.toRingHom ≫ CommRingCat.ofHom e.toRingHom=𝟙 D := by
      apply CommRingCat.hom_ext
      apply RingHom.ext
      intro d
      exact e.apply_symm_apply d
    rw [hh,Spec.map_id]
  have hy' : Spec.map g y=x := by
    rw [hg,Scheme.Hom.comp_apply,hy]
    change (Spec.map (CommRingCat.ofHom e.toRingHom) ≫
      Spec.map (CommRingCat.ofHom e.symm.toRingHom)) x=x
    rw [hid]
    rfl
  refine ⟨B,g,hopen,⟨y,hy'⟩,c,?_,hr⟩
  rw [hJ,Ideal.map_map]
  have hh : g.hom.comp e.toRingHom=f.hom := by
    apply RingHom.ext
    intro a
    change f.hom (e.symm (e a))=f.hom a
    rw [e.symm_apply_apply]
  rw [hh]
  exact hc
end OriginalRegularIdealCover318
