module
public import OpenChartSections318
public section
noncomputable section
namespace OriginalOpenRingRestrictionPath318
open AlgebraicGeometry CategoryTheory Opposite
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X Y Z : Scheme.{u}} (k : Z ⟶ Y) (j : Y ⟶ X) (t : Z ⟶ X)
  [IsOpenImmersion k] [IsOpenImmersion j] [IsOpenImmersion t]
  (h : k ≫ j = t) (W : X.Opens) (hw : t ''ᵁ ⊤ = W)

include h hw in
/-- The literal named path and original image equality determine the
ambient inclusion used by the restriction; no unrelated ring embedding. -/
lemma image_le : W ≤ j ''ᵁ ⊤ := by
  rw [← hw,← h]
  exact OpenChartSections318.imageLE k j

/-- Original regular-function restriction along a named composite chart,
including its exact full-image equality transport. -/
lemma apply (s : Γ(Y,⊤)) :
    X.presheaf.map (homOfLE (image_le k j t h W hw)).op ((j.appIso ⊤).inv s) =
      X.presheaf.map (eqToHom hw.symm).op ((t.appIso ⊤).inv (k.appTop s)) := by
  subst t
  have hp := congrArg (X.presheaf.map (eqToHom hw.symm).op)
    (OpenChartSections318.restriction_apply k j s)
  simpa only [← Functor.map_comp_apply,← op_comp] using hp
end OriginalOpenRingRestrictionPath318
