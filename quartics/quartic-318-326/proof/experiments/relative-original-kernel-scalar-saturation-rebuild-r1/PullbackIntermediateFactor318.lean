module
public import ContactProjectiveUniversalChartRecovery318
public section
noncomputable section
namespace PullbackIntermediateFactor318
open CategoryTheory CategoryTheory.Limits
universe u v
variable {C : Type u} [Category.{v} C] {A B X Y Z W : C}
  (k : A ⟶ X) (q : A ⟶ Y) (r : X ⟶ Z) (a : Y ⟶ W) (b : W ⟶ Z)
  (H : IsPullback k q r (a ≫ b)) (l : B ⟶ X) (s : B ⟶ W) (K : IsPullback l s r b)
/-- The intermediate-family map comes from the ACTUAL outer and right
Cartesian squares. No pointwise factorization is substituted. -/
@[expose] def lift : A ⟶ B := K.lift k (q ≫ a) (by simpa only [Category.assoc] using H.w)
@[reassoc] lemma lift_left : lift k q r a b H l s K ≫ l=k := K.lift_fst _ _ _
@[reassoc] lemma lift_right : lift k q r a b H l s K ≫ s=q ≫ a := K.lift_snd _ _ _
lemma cartesian : IsPullback (lift k q r a b H l s K) q s a := by
  apply IsPullback.of_right (h₁₂ := l) (h₂₂ := b)
  · simpa only [lift_left] using H
  · exact lift_right k q r a b H l s K
  · exact K
end PullbackIntermediateFactor318
