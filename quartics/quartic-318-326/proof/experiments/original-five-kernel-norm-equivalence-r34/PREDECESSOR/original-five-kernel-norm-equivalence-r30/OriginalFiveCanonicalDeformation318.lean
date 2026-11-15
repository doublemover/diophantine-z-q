module
public import OriginalHOneCoverIndependence318
public section
noncomputable section
namespace OriginalFiveCanonicalDeformation318
open AlgebraicGeometry CategoryTheory Opposite
open ContactRelativeLinePresheaf318 OriginalFiveHOnePointedNaturality318
open scoped BigOperators
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
local instance sourceIntegral : IsIntegral ActualSourceHOnePresentation318.Source :=
  ContactProjectiveModel318.model_integral SourceTwistArithmetic318.units
local instance fifthFinite : IsFinite FifthCompletedGlobal318.map := FifthCompletedFinite318.finite
/-- The previously distinct adapted fifth-cover construction is now proved to
be the unchanged canonical contact-cover construction on EVERY original H1 class. -/
lemma fifth_source_eq (z : ActualSourceHOnePullbacks318.SourceHOne) :
    sourceForFifth z = OriginalHOnePointedMaps318.source z :=
  OriginalHOneCoverIndependence318.independent
    (FifthCompletedGlobal318.map ⁻¹ᵁ fifthFiniteOpen) (FifthCompletedGlobal318.map ⁻¹ᵁ fifthInfinityOpen)
    sourceStructure
    ((isAffineOpen_opensRange (WeierstrassGluing318.finiteChart
      FifthCharacterShortPolynomial318.A FifthCharacterShortPolynomial318.B)).preimage FifthCompletedGlobal318.map)
    ((isAffineOpen_opensRange (WeierstrassGluing318.infinityChart
      FifthCharacterShortPolynomial318.A FifthCharacterShortPolynomial318.B)).preimage FifthCompletedGlobal318.map)
    fifth_preimage_cover
    ActualSourceHOnePresentation318.finiteOpen ActualSourceHOnePresentation318.infinityOpen
    ActualSourceHOnePresentation318.finite_affine ActualSourceHOnePresentation318.infinity_affine
    ActualSourceHOnePresentation318.cover z
/-- All five original pullbacks now commute with the SAME actual source
H1-to-pointed map; this is the missing fifth canonical square. -/
lemma fifth_canonical (z : SheafCohomologyRetraction318.structureH FifthCompletedGlobal318.Target 1) :
    OriginalFivePointedDeformations318.fifthPullback (OriginalHOnePointedMaps318.fifth z) =
      OriginalHOnePointedMaps318.source (ActualSourceHOnePullbacks318.fifthPullback z) :=
  (OriginalFiveHOnePointedNaturality318.fifth z).trans (fifth_source_eq _)
lemma fifth_relative (z : SheafCohomologyRetraction318.structureH FifthCompletedGlobal318.Target 1) :
    ContactRelativeLinePresheaf318.fifthPullback.app (op (Over.mk (DualNumberScheme318.structureMap ℚ)))
      (OriginalHOneRelativeHom318.fifth (Multiplicative.ofAdd z)) =
      OriginalHOneRelativeHom318.source (Multiplicative.ofAdd (ActualSourceHOnePullbacks318.fifthPullback z)) := by
  have hh := congrArg (OriginalFivePointedDeformations318.relativeClass sourceStructure) (fifth_canonical z)
  rw [OriginalFivePointedDeformations318.fifth_matches_relative] at hh
  exact hh
/-- Original five-factor addition maps to the product under the original five
relative Picard pullbacks, with no fifth-cover discrepancy remaining. This is a
map identity, not a claim that all deformations have been classified. -/
lemma five_sum
    (z : (a : Fin 4) → SheafCohomologyRetraction318.structureH (CompletedCharacterSchemeMaps318.Target a) 1)
    (w : SheafCohomologyRetraction318.structureH FifthCompletedGlobal318.Target 1) :
    OriginalHOneRelativeHom318.source (Multiplicative.ofAdd
      ((∑ a : Fin 4, ActualSourceHOnePullbacks318.characterPullback a (z a)) +
        ActualSourceHOnePullbacks318.fifthPullback w)) =
    (∏ a : Fin 4, (ContactRelativeLinePresheaf318.characterPullback a).app
      (op (Over.mk (DualNumberScheme318.structureMap ℚ)))
      (OriginalHOneRelativeHom318.character a (Multiplicative.ofAdd (z a)))) *
    ContactRelativeLinePresheaf318.fifthPullback.app (op (Over.mk (DualNumberScheme318.structureMap ℚ)))
      (OriginalHOneRelativeHom318.fifth (Multiplicative.ofAdd w)) := by
  change OriginalHOneRelativeHom318.source
    (Multiplicative.ofAdd (∑ a : Fin 4, ActualSourceHOnePullbacks318.characterPullback a (z a)) *
      Multiplicative.ofAdd (ActualSourceHOnePullbacks318.fifthPullback w)) = _
  rw [map_mul, OriginalHOneRelativeHom318.character_sum, ← fifth_relative]
end OriginalFiveCanonicalDeformation318
