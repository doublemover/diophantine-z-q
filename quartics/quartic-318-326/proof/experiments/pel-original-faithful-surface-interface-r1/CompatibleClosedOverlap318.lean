module
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public section
noncomputable section
namespace CompatibleClosedOverlap318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
variable {X U V W ZU ZV ZW : Scheme.{u}}
  (i : U ⟶ X) (j : V ⟶ X) (l : W ⟶ U) (r : W ⟶ V)
  (a : ZU ⟶ U) (b : ZV ⟶ V) (c : ZW ⟶ W)
  (p : ZW ⟶ ZU) (q : ZW ⟶ ZV)
  (hW : IsPullback l r i j) (hU : IsPullback c p l a) (hV : IsPullback c q r b)
  [Mono a] [Mono b]

/-- Two actual closed subschemes that agree on a genuine ambient
intersection have that SAME intersection as their full scheme pullback. -/
theorem cartesian : IsPullback p q (a≫i) (b≫j) := by
  have hw : p≫a≫i=q≫b≫j := by
    rw [←hU.w_assoc,←hV.w_assoc,hW.w]
  apply IsPullback.mk' hw
  · intro T f g hp hq
    apply hU.hom_ext
    · apply hW.hom_ext
      · rw [Category.assoc,hU.w,Category.assoc,hU.w,←Category.assoc,←Category.assoc,hp]
      · rw [Category.assoc,hV.w,Category.assoc,hV.w,←Category.assoc,←Category.assoc,hq]
    · exact hp
  · intro T f g hfg
    let w := hW.lift (f≫a) (g≫b) (by simpa only [Category.assoc] using hfg)
    let z := hU.lift w f (hW.lift_fst _ _ _)
    refine ⟨z,hU.lift_snd _ _ _,?_⟩
    apply (cancel_mono b).1
    rw [Category.assoc,←hV.w,←Category.assoc,hU.lift_fst,hW.lift_snd]

/-- The literal projections of the full subscheme pullback are open
when the ambient intersection arrows are open. -/
theorem fst_open [IsOpenImmersion l] [IsOpenImmersion r] :
    IsOpenImmersion (pullback.fst (a≫i) (b≫j)) := by
  haveI : IsOpenImmersion p := MorphismProperty.of_isPullback hU inferInstance
  let h := cartesian i j l r a b c p q hW hU hV
  have he : h.isoPullback.inv≫p=pullback.fst (a≫i) (b≫j) := h.isoPullback_inv_fst
  rw [←he]
  infer_instance
end CompatibleClosedOverlap318
