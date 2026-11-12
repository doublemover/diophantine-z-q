module
public import ContactRelationProjectionImage318
public section
noncomputable section
namespace ContactRelationImageBaseChange318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite LineSheafClass318
open ContactOriginalRelativePolynomialCharts318
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ) (L K : Line (curve R c))
local notation "Q" => Spec (CommRingCat.of ℚ)
local notation "B" => Over.mk (baseMap R)
local notation "p" => ContactIntrinsicDifferentials318.structureMap c
local notation "P" => OriginalAbsoluteLinePresheaf318.presheaf p
local notation "π" => ContactRelationProjectionImage318.projection R c L K
variable (T : Over Q) (f : T ⟶ B)
/-- Actual categorical base change of the SAME geometric relation witness.
The object remains a scheme in the relative site even for nonaffine or
nonreduced T; no newly chosen frame parameter is silently substituted. -/
abbrev object := pullback π f
abbrev projection : object R c L K T f ⟶ T := pullback.snd π f
/-- Every base-changed original absolute relation is the image of the
actual pulled-back geometric projection, on ALL further site arrows. -/
lemma equalizer_eq_image :
    Presheaf.equalizerSieve (P.map f.op (classOf L)) (P.map f.op (classOf K))=
      MorphismImageSieve318.image (projection R c L K T f) := by
  rw [←OriginalPicardAbsoluteEquality318.pullback_equalizer,
    ContactRelationProjectionImage318.equalizer_eq_image,
    MorphismImageSieve318.pullback_image]
/-- A whole-site lift into the actual changed relation object is the
same factorization of the original projection; this is native pullback
universality, not a new representability assumption. -/
lemma membership (U : Over Q) (g : U ⟶ T) :
    MorphismImageSieve318.image (projection R c L K T f) g ↔
      MorphismImageSieve318.image π (g ≫ f) := by
  rw [←MorphismImageSieve318.pullback_image]
  rfl
end ContactRelationImageBaseChange318
