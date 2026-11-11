module
public import OriginalTransferDeckNaturality318
public import OriginalFiveHOneEquivalence318

public section
noncomputable section
namespace OriginalFiveTransferInvariance318
open AlgebraicGeometry CategoryTheory SourceTwistArithmetic318
open ActualSourceHOnePullbacks318 ActualSourceHOneTransfers318 ActualQuotientSheafRetraction318
open ActualSourceHOneCharacterAction318 SourceHOneCharacterIndices318
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
local instance shortAffine {R : Type} [CommRing R] (A B : R) :
    IsAffine (ShortAffineScheme318.scheme A B) := by
  dsimp only [ShortAffineScheme318.scheme]
  infer_instance
local instance sourceIntegral : IsIntegral (ContactGlobalSmooth318.Model units) :=
  ContactProjectiveModel318.model_integral units
local instance characterIntegral (i : Fin 4) : IsIntegral (CompletedCharacterSchemeMaps318.Target i) :=
  (CompletedCharacterProper318.target_proper_integral i).2
local instance characterDominant (i : Fin 4) : IsDominant (CompletedCharacterGlobal318.completedMap i) :=
  CompletedCharacterProper318.completedMap_dominant i
local instance characterFinite (i : Fin 4) : IsFinite (CompletedCharacterGlobal318.completedMap i) :=
  CompletedCharacterFinite318.completedMap_finite i
local instance fifthIntegral : IsIntegral FifthCompletedGlobal318.Target :=
  FifthCompletedProper318.target_proper_integral.2
local instance fifthDominant : IsDominant FifthCompletedGlobal318.map := FifthCompletedProper318.dominant
local instance fifthFinite : IsFinite FifthCompletedGlobal318.map := FifthCompletedFinite318.finite

/-- Original normalized transfers are invariant under their actual omitted-root deck involutions. -/
theorem character_invariant (i : Fin 4) (y : SourceHOne) :
    characterTransfer i (action (SourceCharacterFields318.flip i) y) = characterTransfer i y := by
  rw [← ActualSourceHOneGeometricSigns318.geometric_action]
  apply OriginalTransferDeckNaturality318.transfer_invariant
    (CompletedCharacterGlobal318.completedMap i) (characterRetraction i)
    (ContactGlobalSigns318.iso units (SourceCharacterFields318.flip i)) (CharacterSignGlobal318.omitted i)
    _ (OriginalCharacterPullbackLines318.finiteOpen i) (OriginalCharacterPullbackLines318.infinityOpen i)
    (isAffineOpen_opensRange (WeierstrassGluing318.finiteChart (publishedA i) (publishedB i)))
    (isAffineOpen_opensRange (WeierstrassGluing318.infinityChart (publishedA i) (publishedB i)))
    (OriginalCharacterPullbackLines318.target_cover i) y
  intro U s
  rw [character_component,character_component]
  congr 1
  exact OriginalOpenTraceDeck318.trace_invariant (CompletedCharacterGlobal318.completedMap i)
    (ContactGlobalSigns318.iso units (SourceCharacterFields318.flip i))
    (CompletedCharacterTraceBasis318.hasBasis i) (CompletedCharacterTraceBasis318.generic_finite i)
    (CharacterSignGlobal318.omitted i) U s

/-- Every original positive full-root sign leaves the original fifth transfer unchanged on whole H1. -/
theorem fifth_invariant (b : Fin 4 → Bool) (hb : epsilon none b = 1) (y : SourceHOne) :
    fifthTransfer (action b y) = fifthTransfer y := by
  have hs : FifthSignAffine318.sign b = 1 := by
    rw [OriginalFifthPullbackLine318.sign_matches,hb,map_one]
  rw [← ActualSourceHOneGeometricSigns318.geometric_action]
  apply OriginalTransferDeckNaturality318.transfer_invariant
    FifthCompletedGlobal318.map fifthRetraction (ContactGlobalSigns318.iso units b)
    (FifthSignGlobal318.positive b hs) _
    OriginalFifthPullbackLine318.finiteOpen OriginalFifthPullbackLine318.infinityOpen
    (isAffineOpen_opensRange (WeierstrassGluing318.finiteChart
      FifthCharacterShortPolynomial318.A FifthCharacterShortPolynomial318.B))
    (isAffineOpen_opensRange (WeierstrassGluing318.infinityChart
      FifthCharacterShortPolynomial318.A FifthCharacterShortPolynomial318.B))
    OriginalFifthPullbackLine318.target_cover y
  intro U s
  rw [fifth_component,fifth_component]
  congr 1
  exact OriginalOpenTraceDeck318.trace_invariant FifthCompletedGlobal318.map
    (ContactGlobalSigns318.iso units b) FifthTargetNormalBasis318.hasBasis FifthChartTrace318.generic_finite
    (FifthSignGlobal318.positive b hs) U s

end OriginalFiveTransferInvariance318
