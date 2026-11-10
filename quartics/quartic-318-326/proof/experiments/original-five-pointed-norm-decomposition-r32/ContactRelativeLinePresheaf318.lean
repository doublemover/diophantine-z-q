module
public import RelativeLineFunctorPullback318
public import FifthCompletedGlobal318
public section
noncomputable section
namespace ContactRelativeLinePresheaf318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open SourceTwistArithmetic318 RelativeLineClassQuotient318
open RelativeLineFunctorPullback318
abbrev Base := Spec (CommRingCat.of ℚ)

/-- The original rational structure map on the entire contact normalization. -/
@[expose] def sourceStructure : ContactGlobalSmooth318.Model units ⟶ Base :=
  (ContactProjectiveModel318.coverMap units).fromNormalization ≫
    ProjectiveJLine318.structureMap ℚ

@[expose] def characterStructure (i : Fin 4) : CompletedCharacterSchemeMaps318.Target i ⟶ Base :=
  WeierstrassGluing318.structureMap (publishedA i) (publishedB i)

@[expose] def fifthStructure : FifthCompletedGlobal318.Target ⟶ Base :=
  WeierstrassGluing318.structureMap FifthCharacterShortPolynomial318.A FifthCharacterShortPolynomial318.B

/-- The naive relative Picard presheaf of the same original source scheme. -/
@[expose] def source : (Over Base)ᵒᵖ ⥤ CommGrpCat.{1} :=
  RelativeLineClassBaseChange318.presheaf sourceStructure

@[expose] def character (i : Fin 4) : (Over Base)ᵒᵖ ⥤ CommGrpCat.{1} :=
  RelativeLineClassBaseChange318.presheaf (characterStructure i)

@[expose] def fifth : (Over Base)ᵒᵖ ⥤ CommGrpCat.{1} :=
  RelativeLineClassBaseChange318.presheaf fifthStructure

/-- All four actual completed quotient maps induce pullback on their actual
relative presheaves, naturally for every rational scheme test. -/
@[expose] def characterPullback (i : Fin 4) : character i ⟶ source :=
  transformation sourceStructure (characterStructure i)
    (CompletedCharacterGlobal318.completedMap i) (CompletedCharacterGlobal318.over_Q i)

/-- The fifth transformation uses the original full-root completed quotient. -/
@[expose] def fifthPullback : fifth ⟶ source :=
  transformation sourceStructure fifthStructure FifthCompletedGlobal318.map FifthCompletedGlobal318.over_Q

lemma character_on_original_line (i : Fin 4) {T : Scheme} (t : T ⟶ Base)
    (L : LineSheafClass318.Line (pullback (characterStructure i) t)) :
    (characterPullback i).app (op (Over.mk t))
      (classMap (pullback.snd (characterStructure i) t) (LineSheafClass318.classOf L)) =
    classMap (pullback.snd sourceStructure t)
      (LineSheafClass318.classOf (LineSheafPullback318.line
        (baseMap sourceStructure (characterStructure i)
          (CompletedCharacterGlobal318.completedMap i) (CompletedCharacterGlobal318.over_Q i) t) L)) := rfl

lemma fifth_on_original_line {T : Scheme} (t : T ⟶ Base)
    (L : LineSheafClass318.Line (pullback fifthStructure t)) :
    fifthPullback.app (op (Over.mk t))
      (classMap (pullback.snd fifthStructure t) (LineSheafClass318.classOf L)) =
    classMap (pullback.snd sourceStructure t)
      (LineSheafClass318.classOf (LineSheafPullback318.line
        (baseMap sourceStructure fifthStructure FifthCompletedGlobal318.map FifthCompletedGlobal318.over_Q t) L)) := rfl
end ContactRelativeLinePresheaf318
