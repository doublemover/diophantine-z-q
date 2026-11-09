module
public import AdditiveDeformationClasses318
public section
noncomputable section
namespace AdditiveCocycleRefinement318
open AlgebraicGeometry CategoryTheory Opposite InfinitesimalUnitCocycle318
universe u
set_option maxHeartbeats 850000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {X Y : Scheme.{u}} (f : X ⟶ Y)
/-- Actual source and target restrictions commute with the original appLE map
on any proved refinement, not only when the opens are equal inverse images. -/
lemma restrict_appLE {V W : Y.Opens} (h : V ≤ W) {V' W' : X.Opens} (h' : V' ≤ W')
    (hV : V' ≤ f ⁻¹ᵁ V) (hW : W' ≤ f ⁻¹ᵁ W) (a : Γ(Y,W)) :
    restrict X h' (f.appLE W W' hW a) = f.appLE V V' hV (restrict Y h a) := by
  exact congrArg (fun k : Y.presheaf.obj (op W) ⟶ X.presheaf.obj (op V') => k a)
    (show f.appLE W W' hW ≫ X.presheaf.map (homOfLE h').op =
      Y.presheaf.map (homOfLE h).op ≫ f.appLE V V' hV by
      simp only [Scheme.Hom.appLE_map, Scheme.Hom.map_appLE])
variable {ι : Type u} (U : ι → Y.Opens) (V : ι → X.Opens) (hV : ∀ a, V a ≤ f ⁻¹ᵁ U a)
/-- Original additive cocycles transported through actual structure-ring maps
on a full-cover refinement, retaining all double/triple intersections. -/
@[expose] def cocycle (c : AdditiveCocycle Y U) : AdditiveCocycle X V where
  transition a b := f.appLE (U a ⊓ U b) (V a ⊓ V b) (inf_le_inf (hV a) (hV b)) (c.transition a b)
  diagonal a := by rw [c.diagonal, map_zero]
  triple a b d := by
    rw [restrict_appLE f inf_le_left inf_le_left
      (inf_le_inf (inf_le_inf (hV a) (hV b)) (hV d)),
      restrict_appLE f (le_inf (inf_le_left.trans inf_le_right) inf_le_right)
        (le_inf (inf_le_left.trans inf_le_right) inf_le_right)
        (inf_le_inf (inf_le_inf (hV a) (hV b)) (hV d)),
      restrict_appLE f (le_inf (inf_le_left.trans inf_le_left) inf_le_right)
        (le_inf (inf_le_left.trans inf_le_left) inf_le_right)
        (inf_le_inf (inf_le_inf (hV a) (hV b)) (hV d)),
      ← map_add, c.triple]
lemma preserves_coboundary (c d : AdditiveCocycle Y U) (a : ∀ k, Γ(Y,U k))
    (h : ∀ k l, d.transition k l = restrict Y inf_le_left (a k) -
      restrict Y inf_le_right (a l) + c.transition k l) (k l : ι) :
    (cocycle f U V hV d).transition k l =
      restrict X inf_le_left (f.appLE (U k) (V k) (hV k) (a k)) -
      restrict X inf_le_right (f.appLE (U l) (V l) (hV l) (a l)) +
      (cocycle f U V hV c).transition k l := by
  change f.appLE _ _ _ (d.transition k l) = _
  rw [h, map_add, map_sub,
    restrict_appLE f inf_le_left inf_le_left (inf_le_inf (hV k) (hV l)),
    restrict_appLE f inf_le_right inf_le_right (inf_le_inf (hV k) (hV l))]
  rfl
@[expose] def classes : AdditiveDeformationClasses318.Classes Y U →
    AdditiveDeformationClasses318.Classes X V :=
  Quotient.map (cocycle f U V hV) (by
    intro c d h
    obtain ⟨a,ha⟩ := h
    exact ⟨fun k => f.appLE (U k) (V k) (hV k) (a k), preserves_coboundary f U V hV c d a ha⟩)
end AdditiveCocycleRefinement318
