module
public import FlatRingPrincipalRegular318
public import RelativeCartierAffineCartesian318
public section
noncomputable section
namespace RegularClosedFlatPullback318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
variable {Z X W Y : Scheme.{u}} (p : Z ⟶ X) (q : W ⟶ Y)
  (t : W ⟶ Z) (g : Y ⟶ X) [hflat : Flat g]
  (F : IsPullback t q p g)
include F hflat in
/-- Genuine regular quotient charts are stable under flat ambient
pullback, proved on full affine refinements of the actual pulled opens.
This includes the open coefficient restrictions needed for globalization. -/
lemma regular (h : OriginalRegularClosedCharts318.Property p) :
    OriginalRegularClosedCharts318.Property q := by
  intro x
  obtain ⟨A,j,hj,hy,c,z,H,hc⟩ := h (g x)
  letI : IsOpenImmersion j := hj
  have hx : x ∈ Set.range (pullback.snd j g) := by
    change x ∈ (pullback.snd j g).opensRange
    rw [Scheme.Hom.opensRange_pullbackSnd]
    exact hy
  obtain ⟨v,hv⟩ := hx
  obtain ⟨i,w,hw⟩ := (pullback j g).affineOpenCover.openCover.exists_eq v
  let B : CommRingCat := (pullback j g).affineOpenCover.X i
  let k : Spec B ⟶ pullback j g := (pullback j g).affineOpenCover.f i
  let φ : A ⟶ B := Spec.preimage (k ≫ pullback.fst j g)
  letI : Algebra A B := φ.hom.toAlgebra
  have hφ : Spec.map φ=k ≫ pullback.fst j g := Spec.map_preimage _
  letI : Flat (Spec.map φ) := by rw [hφ]; infer_instance
  letI : Module.Flat A B := RingHom.flat_algebraMap_iff.mp (Flat.SpecMap_iff.mp inferInstance)
  let I : Ideal A := Ideal.span ({c} : Set A)
  let J : Ideal B := Ideal.span ({φ.hom c} : Set B)
  have hI : I.map φ.hom=J := by rw [Ideal.map_span,Set.image_singleton]
  let Q := Spec.map (AffineQuotientPushout318.targetMap J)
  let e := Spec.map (AffineQuotientPushout318.arrow φ I J hI)
  let l := k ≫ pullback.snd j g
  have hs : Spec.map φ ≫ j=l ≫ g := by
    rw [hφ,Category.assoc,pullback.condition,← Category.assoc]
  have outer : IsPullback Q (e ≫ z) (l ≫ g) p := by
    rw [← hs]
    exact (AffineQuotientPushout318.pullback φ I J hI).paste_vert H
  let s := F.flip.lift (Q ≫ l) (e ≫ z) (by simpa only [Category.assoc] using outer.w)
  have hsq : s ≫ q=Q ≫ l := F.flip.lift_fst _ _ _
  have hst : s ≫ t=e ≫ z := F.flip.lift_snd _ _ _
  have K : IsPullback Q s l q := by
    apply IsPullback.of_bot (v₂₁ := g) (v₂₂ := p)
    · simpa only [hst] using outer
    · exact hsq.symm
    · exact F.flip
  refine ⟨B,l,inferInstance,⟨w,?_⟩,φ.hom c,s,K,?_⟩
  · change (k ≫ pullback.snd j g) w=x
    rw [Scheme.Hom.comp_apply,hw,hv]
  · exact FlatRingPrincipalRegular318.regular A B c hc
end RegularClosedFlatPullback318
