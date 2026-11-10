module
public import OriginalHOneKernelGroupEquivalence318
public import OriginalFiveCanonicalDeformation318
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public section
noncomputable section
namespace OriginalFivePointedClassification318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open ContactRelativeLinePresheaf318 SourceTwistArithmetic318
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
/-- Separatedness of the ORIGINAL structure map gives affine intersections;
no affine-overlap hypothesis is silently added to the concrete applications. -/
lemma affine_overlap {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of ℚ)) [IsSeparated p]
    {U V : X.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V) : IsAffineOpen (U ⊓ V) := by
  letI : X.IsSeparated := ⟨by
    rw [← terminal.comp_from p]
    infer_instance⟩
  exact hU.inf hV
local instance sourceIntegral : IsIntegral ActualSourceHOnePresentation318.Source :=
  ContactProjectiveModel318.model_integral units
local instance sourceProper : IsProper sourceStructure :=
  (ContactGlobalProper318.proper_integral_extension units).2.2
@[expose] def source : ActualSourceHOnePullbacks318.SourceHOne ≃ OriginalFivePointedDeformations318.SourceClass :=
  OriginalHOnePointedEquivalence318.equivalence sourceStructure
    ActualSourceHOnePresentation318.finiteOpen ActualSourceHOnePresentation318.infinityOpen
    ActualSourceHOnePresentation318.finite_affine ActualSourceHOnePresentation318.infinity_affine
    (affine_overlap sourceStructure ActualSourceHOnePresentation318.finite_affine
      ActualSourceHOnePresentation318.infinity_affine) ActualSourceHOnePresentation318.cover
lemma source_apply (z : ActualSourceHOnePullbacks318.SourceHOne) :
    source z = OriginalHOnePointedMaps318.source z := rfl
variable (A B : ℚ) [IsIntegral (WeierstrassGluing318.scheme A B)]
@[expose] def weierstrass : SheafCohomologyRetraction318.structureH (WeierstrassGluing318.scheme A B) 1 ≃
    DualNumberScheme318.Class ℚ (WeierstrassGluing318.structureMap A B) := by
  letI := CubicClosedImmersion318.structure_separated A B
  exact OriginalHOnePointedEquivalence318.equivalence (WeierstrassGluing318.structureMap A B)
    (OriginalHOnePointedMaps318.finiteOpen A B) (OriginalHOnePointedMaps318.infinityOpen A B)
    (isAffineOpen_opensRange (WeierstrassGluing318.finiteChart A B))
    (isAffineOpen_opensRange (WeierstrassGluing318.infinityChart A B))
    (affine_overlap (WeierstrassGluing318.structureMap A B)
      (isAffineOpen_opensRange (WeierstrassGluing318.finiteChart A B))
      (isAffineOpen_opensRange (WeierstrassGluing318.infinityChart A B)))
    (OriginalHOnePointedMaps318.target_cover A B)
local instance characterIntegral (a : Fin 4) : IsIntegral (CompletedCharacterSchemeMaps318.Target a) :=
  (CompletedCharacterProper318.target_proper_integral a).2
local instance fifthIntegral : IsIntegral FifthCompletedGlobal318.Target :=
  FifthCompletedProper318.target_proper_integral.2
@[expose] def character (a : Fin 4) :
    SheafCohomologyRetraction318.structureH (CompletedCharacterSchemeMaps318.Target a) 1 ≃
      OriginalFivePointedDeformations318.CharacterClass a := weierstrass (publishedA a) (publishedB a)
@[expose] def fifth : SheafCohomologyRetraction318.structureH FifthCompletedGlobal318.Target 1 ≃
    OriginalFivePointedDeformations318.FifthClass :=
  weierstrass FifthCharacterShortPolynomial318.A FifthCharacterShortPolynomial318.B
lemma character_apply (a : Fin 4) (z : SheafCohomologyRetraction318.structureH (CompletedCharacterSchemeMaps318.Target a) 1) :
    character a z = OriginalHOnePointedMaps318.character a z := rfl
lemma fifth_apply (z : SheafCohomologyRetraction318.structureH FifthCompletedGlobal318.Target 1) :
    fifth z = OriginalHOnePointedMaps318.fifth z := rfl
/-- Classification retains the literal original four quotient pullbacks. -/
lemma character_natural (a : Fin 4)
    (z : SheafCohomologyRetraction318.structureH (CompletedCharacterSchemeMaps318.Target a) 1) :
    OriginalFivePointedDeformations318.characterPullback a (character a z) =
      source (ActualSourceHOnePullbacks318.characterPullback a z) :=
  OriginalFiveHOnePointedNaturality318.character a z
/-- The fifth square uses the SAME source classification, by the earlier exact
cover-independence proof, not a new adapted source map. -/
lemma fifth_natural (z : SheafCohomologyRetraction318.structureH FifthCompletedGlobal318.Target 1) :
    OriginalFivePointedDeformations318.fifthPullback (fifth z) =
      source (ActualSourceHOnePullbacks318.fifthPullback z) :=
  OriginalFiveCanonicalDeformation318.fifth_canonical z
end OriginalFivePointedClassification318
