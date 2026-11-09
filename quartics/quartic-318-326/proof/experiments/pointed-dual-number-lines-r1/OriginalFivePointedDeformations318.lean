module
public import DualNumberInfinitesimalLines318
public import ContactRelativeLinePresheaf318
public section
noncomputable section
namespace OriginalFivePointedDeformations318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open DualNumberScheme318 ContactRelativeLinePresheaf318
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {R : Type u} [CommRing R] {X Y : Scheme.{u}}
    (p : X ⟶ base R) (q : Y ⟶ base R)
/-- Forget the specified frame, then use the EXISTING quotient by actual base lines. -/
@[expose] def relativeClass (c : DualNumberScheme318.Class R p) :
    RelativeLineClassQuotient318.RelativeClass (pullback.snd p (structureMap R)) :=
  RelativeLineClassQuotient318.classMap (pullback.snd p (structureMap R))
    (PointedLineDeformation318.forget (reduction R p) c)
lemma relative_pullback (f : X ⟶ Y) (hf : f ≫ q = p) (c : DualNumberScheme318.Class R q) :
    relativeClass p (DualNumberScheme318.pullback R p q f hf c) =
      RelativeLineFunctorPullback318.relativeMap p q f hf (structureMap R) (relativeClass q c) := by
  unfold relativeClass
  rw [DualNumberScheme318.forget_pullback, RelativeLineFunctorPullback318.relativeMap_class]
  rfl
abbrev SourceClass := DualNumberScheme318.Class ℚ sourceStructure
abbrev CharacterClass (a : Fin 4) := DualNumberScheme318.Class ℚ (characterStructure a)
abbrev FifthClass := DualNumberScheme318.Class ℚ fifthStructure
/-- The original four completed quotient maps, on actual pointed first-order lines. -/
@[expose] def characterPullback (a : Fin 4) : CharacterClass a → SourceClass :=
  DualNumberScheme318.pullback ℚ sourceStructure (characterStructure a)
    (CompletedCharacterGlobal318.completedMap a) (CompletedCharacterGlobal318.over_Q a)
/-- The original full-root quotient, with its actual special-fiber square. -/
@[expose] def fifthPullback : FifthClass → SourceClass :=
  DualNumberScheme318.pullback ℚ sourceStructure fifthStructure
    FifthCompletedGlobal318.map FifthCompletedGlobal318.over_Q
lemma character_matches_relative (a : Fin 4) (c : CharacterClass a) :
    relativeClass sourceStructure (characterPullback a c) =
      (ContactRelativeLinePresheaf318.characterPullback a).app
        (op (Over.mk (structureMap ℚ))) (relativeClass (characterStructure a) c) :=
  relative_pullback sourceStructure (characterStructure a)
    (CompletedCharacterGlobal318.completedMap a) (CompletedCharacterGlobal318.over_Q a) c
lemma fifth_matches_relative (c : FifthClass) :
    relativeClass sourceStructure (fifthPullback c) =
      ContactRelativeLinePresheaf318.fifthPullback.app
        (op (Over.mk (structureMap ℚ))) (relativeClass fifthStructure c) :=
  relative_pullback sourceStructure fifthStructure FifthCompletedGlobal318.map FifthCompletedGlobal318.over_Q c
end OriginalFivePointedDeformations318
