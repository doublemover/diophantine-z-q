module
public import SchemeOpenPushout318
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public section
noncomputable section
namespace SchemeClosedOpenPushout318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
variable {U X Y B V P Q : Scheme.{u}}
  (f : U ⟶ X) (g : U ⟶ Y) (i : X ⟶ B) (j : Y ⟶ B)
  [IsOpenImmersion i] [IsOpenImmersion j] (hb : IsPullback f g i j)
  (a : V ⟶ P) (b : V ⟶ Q) [IsOpenImmersion a] [IsOpenImmersion b]
  (p : P ⟶ X) (q : Q ⟶ Y) (r : V ⟶ U)
  (ha : IsPullback a r p f) (hc : IsPullback b r q g)
lemma agree : a ≫ (p ≫ i)=b ≫ (q ≫ j) := by
  rw [← Category.assoc,ha.w,Category.assoc,hb.w,← Category.assoc,← hc.w,Category.assoc]
@[expose] def map : pushout a b ⟶ B := pushout.desc (p ≫ i) (q ≫ j) (agree f g i j hb a b p q r ha hc)
@[reassoc] lemma inl_map : pushout.inl a b ≫ map f g i j hb a b p q r ha hc=p ≫ i := pushout.inl_desc _ _ _
@[reassoc] lemma inr_map : pushout.inr a b ≫ map f g i j hb a b p q r ha hc=q ≫ j := pushout.inr_desc _ _ _
lemma left_cartesian : IsPullback (pushout.inl a b) p (map f g i j hb a b p q r ha hc) i := by
  apply Scheme.isPullback_of_openCover _ _ _ _ (SchemeOpenPushout318.cover a b)
  intro k
  cases k with
  | false =>
    change IsPullback (pullback.snd (pushout.inl a b) (pushout.inl a b))
      (pullback.fst (pushout.inl a b) (pushout.inl a b) ≫ p)
      (pushout.inl a b ≫ map f g i j hb a b p q r ha hc) i
    rw [inl_map]
    let h := IsKernelPair.id_of_mono (pushout.inl a b)
    have ht : IsPullback (𝟙 P) p (p ≫ i) i := IsPullback.of_horiz_isIso_mono ⟨by simp⟩
    apply ht.of_iso h.isoPullback (Iso.refl _) (Iso.refl _) (Iso.refl _)
    · simpa only [Iso.refl_hom,Category.comp_id] using h.isoPullback_hom_snd.symm
    · simp only [Iso.refl_hom,Category.comp_id,← Category.assoc,h.isoPullback_hom_fst,Category.id_comp]
    · simp only [Iso.refl_hom,Category.comp_id,Category.id_comp]
    · simp only [Iso.refl_hom,Category.comp_id,Category.id_comp]
  | true =>
    change IsPullback (pullback.snd (pushout.inl a b) (pushout.inr a b))
      (pullback.fst (pushout.inl a b) (pushout.inr a b) ≫ p)
      (pushout.inr a b ≫ map f g i j hb a b p q r ha hc) i
    rw [inr_map]
    let h := SchemeOpenPushout318.cartesian a b
    have ht := hc.paste_vert hb.flip
    apply ht.of_iso h.isoPullback (Iso.refl _) (Iso.refl _) (Iso.refl _)
    · simpa only [Iso.refl_hom,Category.comp_id] using h.isoPullback_hom_snd.symm
    · simp only [Iso.refl_hom,Category.comp_id,← Category.assoc,h.isoPullback_hom_fst]
      exact ha.w.symm
    · simp only [Iso.refl_hom,Category.comp_id,Category.id_comp]
    · simp only [Iso.refl_hom,Category.comp_id,Category.id_comp]
lemma right_cartesian : IsPullback (pushout.inr a b) q (map f g i j hb a b p q r ha hc) j := by
  apply Scheme.isPullback_of_openCover _ _ _ _ (SchemeOpenPushout318.cover a b)
  intro k
  cases k with
  | false =>
    change IsPullback (pullback.snd (pushout.inr a b) (pushout.inl a b))
      (pullback.fst (pushout.inr a b) (pushout.inl a b) ≫ q)
      (pushout.inl a b ≫ map f g i j hb a b p q r ha hc) j
    rw [inl_map]
    let h := (SchemeOpenPushout318.cartesian a b).flip
    have ht := ha.paste_vert hb
    apply ht.of_iso h.isoPullback (Iso.refl _) (Iso.refl _) (Iso.refl _)
    · simpa only [Iso.refl_hom,Category.comp_id] using h.isoPullback_hom_snd.symm
    · simp only [Iso.refl_hom,Category.comp_id,← Category.assoc,h.isoPullback_hom_fst]
      exact hc.w.symm
    · simp only [Iso.refl_hom,Category.comp_id,Category.id_comp]
    · simp only [Iso.refl_hom,Category.comp_id,Category.id_comp]
  | true =>
    change IsPullback (pullback.snd (pushout.inr a b) (pushout.inr a b))
      (pullback.fst (pushout.inr a b) (pushout.inr a b) ≫ q)
      (pushout.inr a b ≫ map f g i j hb a b p q r ha hc) j
    rw [inr_map]
    let h := IsKernelPair.id_of_mono (pushout.inr a b)
    have ht : IsPullback (𝟙 Q) q (q ≫ j) j := IsPullback.of_horiz_isIso_mono ⟨by simp⟩
    apply ht.of_iso h.isoPullback (Iso.refl _) (Iso.refl _) (Iso.refl _)
    · simpa only [Iso.refl_hom,Category.comp_id] using h.isoPullback_hom_snd.symm
    · simp only [Iso.refl_hom,Category.comp_id,← Category.assoc,h.isoPullback_hom_fst,Category.id_comp]
    · simp only [Iso.refl_hom,Category.comp_id,Category.id_comp]
    · simp only [Iso.refl_hom,Category.comp_id,Category.id_comp]
end SchemeClosedOpenPushout318
