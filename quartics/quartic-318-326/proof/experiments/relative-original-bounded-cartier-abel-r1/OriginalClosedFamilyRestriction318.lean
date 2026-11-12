module
public import ClosedFamilyBaseRestriction318
public section
noncomputable section
namespace OriginalClosedFamilyRestriction318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
variable {X B S T Y : Scheme.{u}} (p : X ⟶ B) (b : S ⟶ B) (a : T ⟶ B)
  (f : T ⟶ S) (hf : f ≫ b=a) (q : Y ⟶ pullback p b) [IsClosedImmersion q]
local notation "π" => q ≫ pullback.snd p b
local notation "m" => RelativeSchemeCoefficient318.map p b a f hf
abbrev family := pullback π f
abbrev toFamily : family p b f q ⟶ Y := pullback.fst π f
abbrev projection : family p b f q ⟶ T := pullback.snd π f
/-- Restrict the whole original closed family, retaining the literal
p-first original source over the new arbitrary coefficient scheme. -/
@[expose] def into : family p b f q ⟶ pullback p a :=
  (RelativeSchemeCoefficient318.cartesian p b a f hf).lift
    (toFamily p b f q ≫ q) (projection p b f q)
    (by rw [Category.assoc]; exact pullback.condition)
@[reassoc] lemma into_map : into p b a f hf q ≫ m=toFamily p b f q ≫ q :=
  (RelativeSchemeCoefficient318.cartesian p b a f hf).lift_fst _ _ _
@[reassoc] lemma into_base : into p b a f hf q ≫ pullback.snd p a=projection p b f q :=
  (RelativeSchemeCoefficient318.cartesian p b a f hf).lift_snd _ _ _
lemma cartesian : IsPullback (toFamily p b f q) (into p b a f hf q) q m := by
  apply IsPullback.of_bot (v₂₁ := pullback.snd p a) (v₂₂ := pullback.snd p b)
  · simpa only [into_base] using IsPullback.of_hasPullback π f
  · exact (into_map p b a f hf q).symm
  · exact RelativeSchemeCoefficient318.cartesian p b a f hf
instance closed : IsClosedImmersion (into p b a f hf q) :=
  MorphismProperty.of_isPullback (cartesian p b a f hf q) inferInstance
@[reassoc] lemma into_original : into p b a f hf q ≫ pullback.fst p a=
    toFamily p b f q ≫ q ≫ pullback.fst p b := by
  rw [← RelativeSchemeCoefficient318.map_fst p b a f hf,← Category.assoc,into_map,Category.assoc]
/-- Canonical lift of every actual local whole-family base model. -/
@[expose] def lift {V L : Scheme.{u}} (g : L ⟶ T) (s : V ⟶ L) (k : V ⟶ Y)
    (H : IsPullback k s π (g ≫ f)) : V ⟶ family p b f q :=
  ClosedFamilyBaseRestriction318.lift (pullback.snd p b) q f g s k H
@[reassoc] lemma lift_fst {V L : Scheme.{u}} (g : L ⟶ T) (s : V ⟶ L) (k : V ⟶ Y)
    (H : IsPullback k s π (g ≫ f)) : lift p b f q g s k H ≫ toFamily p b f q=k :=
  ClosedFamilyBaseRestriction318.lift_fst _ _ _ _ _ _ _
@[reassoc] lemma lift_snd {V L : Scheme.{u}} (g : L ⟶ T) (s : V ⟶ L) (k : V ⟶ Y)
    (H : IsPullback k s π (g ≫ f)) : lift p b f q g s k H ≫ projection p b f q=s ≫ g :=
  ClosedFamilyBaseRestriction318.lift_snd _ _ _ _ _ _ _
lemma lift_cartesian {V L : Scheme.{u}} (g : L ⟶ T) (s : V ⟶ L) (k : V ⟶ Y)
    (H : IsPullback k s π (g ≫ f)) :
    IsPullback (lift p b f q g s k H) s (projection p b f q) g :=
  ClosedFamilyBaseRestriction318.lift_cartesian _ _ _ _ _ _ _
end OriginalClosedFamilyRestriction318
