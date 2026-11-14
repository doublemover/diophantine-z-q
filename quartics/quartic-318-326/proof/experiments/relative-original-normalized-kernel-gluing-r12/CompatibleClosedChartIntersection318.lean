module
public import SchemeClosedCoverGluing318
public section
noncomputable section
namespace CompatibleClosedChartIntersection318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
variable {X U V O A B W : Scheme.{u}}
  (i : U ⟶ X) (j : V ⟶ X) (l : O ⟶ U) (r : O ⟶ V)
  (ha : IsPullback l r i j) (q : A ⟶ U) (s : B ⟶ V)
  (a : W ⟶ A) (b : W ⟶ B) (w : W ⟶ O)
  (hl : IsPullback a w q l) (hr : IsPullback b w s r)
  [Mono q]
include ha hl hr in
/-- The actual restriction square obtained by pasting the TWO supplied
closed-family squares with the genuine ambient chart intersection. -/
lemma restriction : IsPullback b (a ≫ q) (s ≫ j) i := by
  have h := hr.paste_vert ha.flip
  simpa only [←hl.w] using h
include ha hl hr in
/-- The overlap is consequently the TRUE ambient fiber product of the
local closed subschemes. This is what supplies categorical triple coherence. -/
lemma intersection : IsPullback a b (q ≫ i) (s ≫ j) :=
  MonoFactorPullback318.square a b q i (s ≫ j)
    (restriction i j l r ha q s a b w hl hr)
include hl hr ha in
lemma first_open [IsOpenImmersion a] :
    IsOpenImmersion (pullback.fst (q ≫ i) (s ≫ j)) := by
  let H := intersection i j l r ha q s a b w hl hr
  have h : IsOpenImmersion (H.isoPullback.inv ≫ a) := inferInstance
  simpa only [H.isoPullback_inv_fst] using h
include ha hl hr in
/-- Exact native-pullback form required by closed-cover descent. -/
lemma actual_restriction : IsPullback (pullback.snd (q ≫ i) (s ≫ j))
    (pullback.fst (q ≫ i) (s ≫ j) ≫ q) (s ≫ j) i := by
  let H := intersection i j l r ha q s a b w hl hr
  apply (restriction i j l r ha q s a b w hl hr).of_iso H.isoPullback
    (Iso.refl _) (Iso.refl _) (Iso.refl _)
  · simpa only [Iso.refl_hom,Category.comp_id] using H.isoPullback_hom_snd.symm
  · simp only [Iso.refl_hom,Category.comp_id,←Category.assoc,H.isoPullback_hom_fst]
  · simp only [Iso.refl_hom,Category.id_comp,Category.comp_id]
  · simp only [Iso.refl_hom,Category.id_comp,Category.comp_id]

end CompatibleClosedChartIntersection318
