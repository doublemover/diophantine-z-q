module
public import RelativeFppfLineLocal318
public import ContactRelativeLinePresheaf318
public section
noncomputable section
namespace ContactFppfLineSheaf318
open AlgebraicGeometry CategoryTheory
open ContactRelativeLinePresheaf318

/-- The associated fppf group sheaf of the same original contact normalization. -/
@[expose] def source : Sheaf (RelativeFppfLineSheaf318.topology Base) CommGrpCat.{1} :=
  RelativeFppfLineSheaf318.sheaf sourceStructure

@[expose] def character (i : Fin 4) :
    Sheaf (RelativeFppfLineSheaf318.topology Base) CommGrpCat.{1} :=
  RelativeFppfLineSheaf318.sheaf (characterStructure i)

@[expose] def fifth : Sheaf (RelativeFppfLineSheaf318.topology Base) CommGrpCat.{1} :=
  RelativeFppfLineSheaf318.sheaf fifthStructure

/-- Sheafification of each original completed-quotient pullback, on the big
fppf site over Q. This is not a morphism of representing schemes. -/
@[expose] def characterPullback (i : Fin 4) : character i ⟶ source :=
  RelativeFppfLineSheaf318.pullback sourceStructure (characterStructure i)
    (CompletedCharacterGlobal318.completedMap i) (CompletedCharacterGlobal318.over_Q i)

@[expose] def fifthPullback : fifth ⟶ source :=
  RelativeFppfLineSheaf318.pullback sourceStructure fifthStructure
    FifthCompletedGlobal318.map FifthCompletedGlobal318.over_Q

/-- The full diagram uses the unchanged presheaf pullback and canonical units. -/
lemma character_unit (i : Fin 4) :
    ContactRelativeLinePresheaf318.characterPullback i ≫
        RelativeFppfLineSheaf318.unit sourceStructure =
      RelativeFppfLineSheaf318.unit (characterStructure i) ≫ (characterPullback i).hom :=
  RelativeFppfLineSheaf318.unit_pullback sourceStructure (characterStructure i)
    (CompletedCharacterGlobal318.completedMap i) (CompletedCharacterGlobal318.over_Q i)

lemma fifth_unit :
    ContactRelativeLinePresheaf318.fifthPullback ≫ RelativeFppfLineSheaf318.unit sourceStructure =
      RelativeFppfLineSheaf318.unit fifthStructure ≫ fifthPullback.hom :=
  RelativeFppfLineSheaf318.unit_pullback sourceStructure fifthStructure
    FifthCompletedGlobal318.map FifthCompletedGlobal318.over_Q

lemma character_unique (i : Fin 4) (g : character i ⟶ source)
    (h : RelativeFppfLineSheaf318.unit (characterStructure i) ≫ g.hom =
      ContactRelativeLinePresheaf318.characterPullback i ≫
        RelativeFppfLineSheaf318.unit sourceStructure) : g = characterPullback i :=
  RelativeFppfLineSheaf318.pullback_unique sourceStructure (characterStructure i)
    (CompletedCharacterGlobal318.completedMap i) (CompletedCharacterGlobal318.over_Q i) g h

lemma fifth_unique (g : fifth ⟶ source)
    (h : RelativeFppfLineSheaf318.unit fifthStructure ≫ g.hom =
      ContactRelativeLinePresheaf318.fifthPullback ≫ RelativeFppfLineSheaf318.unit sourceStructure) :
    g = fifthPullback :=
  RelativeFppfLineSheaf318.pullback_unique sourceStructure fifthStructure
    FifthCompletedGlobal318.map FifthCompletedGlobal318.over_Q g h
end ContactFppfLineSheaf318
