module
public import SchemeClosedFamilyLocalModels318
public section
noncomputable section
namespace ClosedFamilyBaseRestriction318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
variable {X Y B T : Scheme.{u}} (p : X ⟶ B) (q : Y ⟶ X) [IsClosedImmersion q] (f : T ⟶ B)
abbrev ambient := pullback p f
abbrev family := pullback (q ≫ p) f
abbrev toFamily : family p q f ⟶ Y := pullback.fst (q ≫ p) f
abbrev projection : family p q f ⟶ T := pullback.snd (q ≫ p) f
@[expose] def into : family p q f ⟶ ambient p f :=
  pullback.lift (toFamily p q f ≫ q) (projection p q f)
    (by rw [Category.assoc]; exact pullback.condition)
@[reassoc] lemma into_fst : into p q f ≫ pullback.fst p f=toFamily p q f ≫ q := pullback.lift_fst _ _ _
@[reassoc] lemma into_snd : into p q f ≫ pullback.snd p f=projection p q f := pullback.lift_snd _ _ _
lemma cartesian : IsPullback (toFamily p q f) (into p q f) q (pullback.fst p f) := by
  apply IsPullback.of_bot (v₂₁ := pullback.snd p f) (v₂₂ := p)
  · simpa only [into_snd] using IsPullback.of_hasPullback (q ≫ p) f
  · exact (into_fst p q f).symm
  · exact IsPullback.of_hasPullback p f
instance closed : IsClosedImmersion (into p q f) := MorphismProperty.of_isPullback (cartesian p q f) inferInstance
/-- A genuine local model of the original family gives a map to this
actual coefficient restriction by the canonical pullback universal property. -/
@[expose] def lift {V L : Scheme.{u}} (g : L ⟶ T) (s : V ⟶ L) (k : V ⟶ Y)
    (H : IsPullback k s (q ≫ p) (g ≫ f)) : V ⟶ family p q f :=
  pullback.lift k (s ≫ g) (by simpa only [Category.assoc] using H.w)
@[reassoc] lemma lift_fst {V L : Scheme.{u}} (g : L ⟶ T) (s : V ⟶ L) (k : V ⟶ Y)
    (H : IsPullback k s (q ≫ p) (g ≫ f)) : lift p q f g s k H ≫ toFamily p q f=k := pullback.lift_fst _ _ _
@[reassoc] lemma lift_snd {V L : Scheme.{u}} (g : L ⟶ T) (s : V ⟶ L) (k : V ⟶ Y)
    (H : IsPullback k s (q ≫ p) (g ≫ f)) : lift p q f g s k H ≫ projection p q f=s ≫ g := pullback.lift_snd _ _ _
lemma lift_cartesian {V L : Scheme.{u}} (g : L ⟶ T) (s : V ⟶ L) (k : V ⟶ Y)
    (H : IsPullback k s (q ≫ p) (g ≫ f)) : IsPullback (lift p q f g s k H) s (projection p q f) g := by
  apply IsPullback.of_right (h₁₂ := toFamily p q f) (h₂₂ := f)
  · simpa only [lift_fst] using H
  · exact lift_snd p q f g s k H
  · exact IsPullback.of_hasPullback (q ≫ p) f
end ClosedFamilyBaseRestriction318
