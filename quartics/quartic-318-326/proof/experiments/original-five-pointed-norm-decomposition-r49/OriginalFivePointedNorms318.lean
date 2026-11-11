module
public import CanonicalPointedNorm318
public section
noncomputable section
namespace OriginalFivePointedNorms318
open AlgebraicGeometry CategoryTheory
open ContactRelativeLinePresheaf318 SourceTwistArithmetic318
open OriginalHOnePointedMaps318 OriginalFivePointedDeformations318
open ActualFiveHOneDecomposition318 ActualSourceHOnePullbacks318
set_option maxHeartbeats 1700000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
local instance sourceIntegral : IsIntegral ActualSourceHOnePresentation318.Source :=
  ContactProjectiveModel318.model_integral units
local instance characterIntegral (i : Fin 4) : IsIntegral (CompletedCharacterSchemeMaps318.Target i) :=
  (CompletedCharacterProper318.target_proper_integral i).2
local instance characterFinite (i : Fin 4) : IsFinite (CompletedCharacterGlobal318.completedMap i) :=
  CompletedCharacterFinite318.completedMap_finite i
local instance characterDominant (i : Fin 4) : IsDominant (CompletedCharacterGlobal318.completedMap i) :=
  CompletedCharacterProper318.completedMap_dominant i
local instance fifthIntegral : IsIntegral FifthCompletedGlobal318.Target := FifthCompletedProper318.target_proper_integral.2
local instance fifthFinite : IsFinite FifthCompletedGlobal318.map := FifthCompletedFinite318.finite
local instance fifthDominant : IsDominant FifthCompletedGlobal318.map := FifthCompletedProper318.dominant
abbrev TargetClass : Index → Type
  | none => FifthClass
  | some i => CharacterClass i
@[expose] def classification : (i : Index) → TargetHOne i ≃ TargetClass i
  | none => OriginalFivePointedClassification318.fifth
  | some i => OriginalFivePointedClassification318.character i
@[expose] def pullback : (i : Index) → TargetClass i → SourceClass
  | none => fifthPullback
  | some i => characterPullback i
lemma pullback_classification (i : Index) (z : TargetHOne i) :
    pullback i (classification i z) = OriginalFivePointedClassification318.source
      (ActualFiveHOneDecomposition318.pullback i z) := by
  cases i with
  | none => exact OriginalFivePointedClassification318.fifth_natural z
  | some j => exact OriginalFivePointedClassification318.character_natural j z
variable (A B : ℚ) [IsIntegral (WeierstrassGluing318.scheme A B)]
    (f : ActualSourceHOnePresentation318.Source ⟶ WeierstrassGluing318.scheme A B)
    [IsDominant f] [IsFinite f] (hf : f ≫ WeierstrassGluing318.structureMap A B = sourceStructure)
    (hY : NormalAffineBasis318.HasBasis (WeierstrassGluing318.scheme A B))
    (hfinite : letI := AffineDominantNorm318.fieldAlgebra f
      FiniteDimensional (WeierstrassGluing318.scheme A B).functionField ActualSourceHOnePresentation318.Source.functionField)
local instance targetSeparated : IsSeparated (WeierstrassGluing318.structureMap A B) :=
  CubicClosedImmersion318.structure_separated A B
@[expose] def weierstrassNorm : SourceClass → DualNumberScheme318.Class ℚ (WeierstrassGluing318.structureMap A B) :=
  OriginalPointedNormTrace318.norm sourceStructure (WeierstrassGluing318.structureMap A B) f hY hfinite
    (finiteOpen A B) (infinityOpen A B)
    (isAffineOpen_opensRange (WeierstrassGluing318.finiteChart A B))
    (isAffineOpen_opensRange (WeierstrassGluing318.infinityChart A B))
    (OriginalFivePointedClassification318.affine_overlap (WeierstrassGluing318.structureMap A B)
      (isAffineOpen_opensRange (WeierstrassGluing318.finiteChart A B))
      (isAffineOpen_opensRange (WeierstrassGluing318.infinityChart A B))) (target_cover A B) hf
lemma weierstrass_square (z : SourceHOne) :
    weierstrassNorm A B f hf hY hfinite (OriginalFivePointedClassification318.source z) =
      OriginalFivePointedClassification318.weierstrass A B
        (AffineHOneComparison318.transfer f (OriginalPointedNormTrace318.traceSheaf f hY hfinite) z) :=
  CanonicalPointedNorm318.on_source_cover sourceStructure (WeierstrassGluing318.structureMap A B) f hY hfinite
    (finiteOpen A B) (infinityOpen A B)
    (isAffineOpen_opensRange (WeierstrassGluing318.finiteChart A B))
    (isAffineOpen_opensRange (WeierstrassGluing318.infinityChart A B))
    (OriginalFivePointedClassification318.affine_overlap (WeierstrassGluing318.structureMap A B)
      (isAffineOpen_opensRange (WeierstrassGluing318.finiteChart A B))
      (isAffineOpen_opensRange (WeierstrassGluing318.infinityChart A B))) (target_cover A B) hf
    ActualSourceHOnePresentation318.finiteOpen ActualSourceHOnePresentation318.infinityOpen
    ActualSourceHOnePresentation318.finite_affine ActualSourceHOnePresentation318.infinity_affine
    ActualSourceHOnePresentation318.cover z
/-- Genuine determinant-transition norms for all FIVE original quotient maps. -/
@[expose] def norm : (i : Index) → SourceClass → TargetClass i
  | none => weierstrassNorm FifthCharacterShortPolynomial318.A FifthCharacterShortPolynomial318.B
      FifthCompletedGlobal318.map FifthCompletedGlobal318.over_Q FifthTargetNormalBasis318.hasBasis
      FifthChartTrace318.generic_finite
  | some i => weierstrassNorm (publishedA i) (publishedB i) (CompletedCharacterGlobal318.completedMap i)
      (CompletedCharacterGlobal318.over_Q i) (CompletedCharacterTraceBasis318.hasBasis i)
      (CompletedCharacterTraceBasis318.generic_finite i)
/-- SAME canonical contact source and SAME original raw trace for every factor.
The degree-eight normalization has NOT been silently absorbed. -/
lemma norm_classification (i : Index) (z : SourceHOne) :
    norm i (OriginalFivePointedClassification318.source z) =
      classification i (OriginalHOneTraceNormalization318.originalTrace i z) := by
  cases i with
  | none => exact weierstrass_square _ _ FifthCompletedGlobal318.map FifthCompletedGlobal318.over_Q
      FifthTargetNormalBasis318.hasBasis FifthChartTrace318.generic_finite z
  | some j => exact weierstrass_square _ _ (CompletedCharacterGlobal318.completedMap j)
      (CompletedCharacterGlobal318.over_Q j) (CompletedCharacterTraceBasis318.hasBasis j)
      (CompletedCharacterTraceBasis318.generic_finite j) z
end OriginalFivePointedNorms318
