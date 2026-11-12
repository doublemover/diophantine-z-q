module
public import OriginalRegularIdealCover318
public section
noncomputable section
namespace OriginalRegularClosedCharts318
open AlgebraicGeometry CategoryTheory
universe u

/-- The actual scheme-theoretic Cartier chart condition: each target
point has an open affine neighborhood on which the SAME closed subscheme
is the quotient by one non-zero-divisor, certified by a Cartesian square.
This is not merely a condition on the underlying support. -/
@[expose] def Property {Z X : Scheme.{u}} (p : Z ⟶ X) : Prop :=
  ∀ x : X, ∃ (A : CommRingCat.{u}) (j : Spec A ⟶ X),
    IsOpenImmersion j ∧ x ∈ Set.range j ∧
    ∃ (c : A) (z : Spec (CommRingCat.of (A ⧸ Ideal.span {c})) ⟶ Z),
      IsPullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {c})))) z j p ∧
      ∀ a : A, a*c=0 → a=0

lemma quotient (A : CommRingCat.{u}) (I : Ideal A)
    (h : OriginalRegularIdealCover318.Property A I) :
    Property (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) := by
  intro x
  obtain ⟨B,f,hf,hx,c,hc,hr⟩ := h x
  refine ⟨B,Spec.map f,hf,hx,c,
    Spec.map (AffineQuotientPullback318.arrow f I (Ideal.span {c}) hc.symm),?_,hr⟩
  exact AffineQuotientPullback318.pullback_square f I (Ideal.span {c}) hc.symm

/-- Target-open gluing of actual quotient pullback charts. The quotient
maps, regular equations and full Cartesian squares survive composition. -/
lemma glue {Z X : Scheme.{u}} (p : Z ⟶ X) {ι : Type u}
    (U Y : ι → Scheme.{u}) (j : ∀ i,U i ⟶ X) (q : ∀ i,Y i ⟶ U i)
    (z : ∀ i,Y i ⟶ Z) (ho : ∀ i,IsOpenImmersion (j i))
    (cover : ∀ x : X,∃ i, x ∈ Set.range (j i))
    (hs : ∀ i,IsPullback (q i) (z i) (j i) p)
    (h : ∀ i,Property (q i)) : Property p := by
  intro x
  obtain ⟨i,y,hy⟩ := cover x
  obtain ⟨A,k,hk,⟨a,ha⟩,c,w,hw,hr⟩ := h i y
  haveI : IsOpenImmersion k := hk
  haveI : IsOpenImmersion (j i) := ho i
  refine ⟨A,k ≫ j i,inferInstance,⟨a,?_⟩,c,w ≫ z i,hw.paste_vert (hs i),hr⟩
  rw [Scheme.Hom.comp_apply,ha,hy]
end OriginalRegularClosedCharts318
