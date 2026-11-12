module
public import ContactPicardSourceUnionCanonical318
public import WholeAffineTargetFunctions318
public section
noncomputable section
namespace TwoOpenSectionRingUniversal318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
variable {U V X N : Scheme.{u}} (a : U ⟶ X) (b : V ⟶ X)
  [IsOpenImmersion a] [IsOpenImmersion b]
variable (l : N ⟶ U) (r : N ⟶ V) (H : IsPullback l r a b)
open TwoOpenSourceUnion318 WholeAffineTargetFunctions318
variable (T : CommRingCat.{u}) (f : T ⟶ Γ(U,⊤)) (g : T ⟶ Γ(V,⊤))
  (h : f≫l.appTop=g≫r.appTop)
include h in
lemma compatible : l≫realize T f=r≫realize T g := by
  apply (equivalence T).injective
  simp only [equivalence,source,ringMap_realize]
  exact h
/-- Glue actual whole regular functions as maps to an affine target.
No rational functions or reducedness enters this universal property. -/
def lift : T ⟶ Γ(scheme a b,⊤) := ringMap T
  (TwoOpenSourceUnionGluing318.map a b l r H (realize T f) (realize T g)
    (compatible l r T f g h))
@[reassoc] lemma lift_left : lift a b l r H T f g h≫(left a b).appTop=f := by
  rw [lift,←source,TwoOpenSourceUnionGluing318.left_map,ringMap_realize]
@[reassoc] lemma lift_right : lift a b l r H T f g h≫(right a b).appTop=g := by
  rw [lift,←source,TwoOpenSourceUnionGluing318.right_map,ringMap_realize]
lemma unique (q : T ⟶ Γ(scheme a b,⊤))
    (hq : q≫(left a b).appTop=f) (hr : q≫(right a b).appTop=g) :
    q=lift a b l r H T f g h := by
  apply (equivalence T).symm.injective
  change realize T q=realize T (lift a b l r H T f g h)
  apply (cover a b).hom_ext
  intro i
  cases i
  · apply (equivalence T).injective
    change ringMap T (left a b≫realize T q)=_
    rw [source,source,ringMap_realize,ringMap_realize,hq,lift_left]
  · apply (equivalence T).injective
    change ringMap T (right a b≫realize T q)=_
    rw [source,source,ringMap_realize,ringMap_realize,hr,lift_right]
/-- Joint faithfulness for actual top-section ring maps follows from
whole scheme gluing, not a pointwise comparison. -/
lemma hom_ext (q q' : T ⟶ Γ(scheme a b,⊤))
    (hq : q≫(left a b).appTop=q'≫(left a b).appTop)
    (hr : q≫(right a b).appTop=q'≫(right a b).appTop) : q=q' := by
  apply (equivalence T).symm.injective
  apply (cover a b).hom_ext
  intro i
  cases i
  · apply (equivalence T).injective
    simpa only [equivalence,source,ringMap_realize] using hq
  · apply (equivalence T).injective
    simpa only [equivalence,source,ringMap_realize] using hr
end TwoOpenSectionRingUniversal318
