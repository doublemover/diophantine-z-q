module
public import ClosedFamilyCartesianModel318
public section
noncomputable section
namespace ClosedFamilyIteratedCartesian318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
variable {Z X B T U : Scheme.{u}} (p : Z ⟶ X) [IsClosedImmersion p]
  (a : X ⟶ B) (f : T ⟶ B) (k : U ⟶ T)
local notation "P" => ClosedFamilyBaseRestriction318.into a p f
local notation "b" => pullback.snd a f
abbrev ambient := pullback b k
abbrev family := ClosedFamilyBaseRestriction318.family b P k
abbrev into := ClosedFamilyBaseRestriction318.into b P k
abbrev original := pullback.fst b k ≫ pullback.fst a f
abbrev toFamily := ClosedFamilyBaseRestriction318.toFamily b P k ≫ ClosedFamilyBaseRestriction318.toFamily a p f
lemma ambient_cartesian : IsPullback (original a f k) (pullback.snd b k) a (k ≫ f) :=
  ((IsPullback.of_hasPullback b k).flip.paste_vert (IsPullback.of_hasPullback a f).flip).flip
lemma family_cartesian : IsPullback (toFamily p a f k) (into p a f k) p (original a f k) :=
  ((ClosedFamilyBaseRestriction318.cartesian b P k).flip.paste_vert
    (ClosedFamilyBaseRestriction318.cartesian a p f).flip).flip
/-- The true iterated restriction has the same full source-preserving
Cartesian model as direct coefficient composition. -/
@[expose] def comparison : family p a f k ≅ ClosedFamilyBaseRestriction318.family a p (k ≫ f) :=
  ClosedFamilyCartesianModel318.familyIso p a (k ≫ f) (into p a f k) (toFamily p a f k)
    (original a f k) (pullback.snd b k) (family_cartesian p a f k) (ambient_cartesian a f k)
end ClosedFamilyIteratedCartesian318
