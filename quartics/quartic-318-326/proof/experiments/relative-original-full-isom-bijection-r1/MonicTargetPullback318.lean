module
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public section
noncomputable section
namespace MonicTargetPullback318
open CategoryTheory CategoryTheory.Limits
universe u v
variable {C : Type u} [Category.{v} C] {W X Y Z T : C}
  (l : W ⟶ X) (r : W ⟶ Y) (f : X ⟶ Z) (g : Y ⟶ Z) (m : Z ⟶ T) [Mono m]

/-- An actual pullback over a larger ambient target is still the actual
pullback over a specified monomorphic subtarget. Both projections remain
unchanged; no pointwise criterion replaces the universal property. -/
lemma cancel (h : IsPullback l r (f ≫ m) (g ≫ m)) : IsPullback l r f g := by
  have w : l ≫ f=r ≫ g := (cancel_mono m).mp (by simpa only [Category.assoc] using h.w)
  let lift (s : PullbackCone f g) : s.pt ⟶ W :=
    h.lift s.fst s.snd (by simpa only [Category.assoc] using congrArg (fun a => a ≫ m) s.condition)
  apply IsPullback.of_isLimit' ⟨w⟩
  refine PullbackCone.IsLimit.mk _ lift ?_ ?_ ?_
  · intro s
    exact h.lift_fst _ _ _
  · intro s
    exact h.lift_snd _ _ _
  · intro s a ha hb
    exact h.hom_ext (ha.trans (h.lift_fst _ _ _).symm)
      (hb.trans (h.lift_snd _ _ _).symm)
end MonicTargetPullback318
