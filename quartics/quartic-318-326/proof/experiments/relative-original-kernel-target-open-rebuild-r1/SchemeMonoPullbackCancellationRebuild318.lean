module
public import MonicTargetPullback318
public section
noncomputable section
namespace SchemeMonoPullbackCancellationRebuild318
open CategoryTheory CategoryTheory.Limits
universe u v
variable {C : Type u} [Category.{v} C] {W X Y Z B : C}
  {a : W ⟶ X} {b : W ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
  (j : Z ⟶ B) [Mono j]
/-- Reuse the existing exact monomorphic-target cancellation theorem.
The full categorical universal property, not only point equality, is retained. -/
lemma square (H : IsPullback a b (f ≫ j) (g ≫ j)) : IsPullback a b f g :=
  MonicTargetPullback318.cancel a b f g j H
end SchemeMonoPullbackCancellationRebuild318
