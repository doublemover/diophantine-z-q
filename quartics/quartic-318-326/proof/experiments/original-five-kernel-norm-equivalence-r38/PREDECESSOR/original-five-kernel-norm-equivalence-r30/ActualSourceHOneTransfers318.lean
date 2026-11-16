module
public import AffineHOneComparison318
public import ActualSourceHOnePullbacks318
public import CompletedCharacterFinite318
public import FifthCompletedFinite318

public section
noncomputable section
namespace ActualSourceHOneTransfers318
open AlgebraicGeometry CategoryTheory
open SheafCohomologyRetraction318 ActualQuotientSheafRetraction318 ActualSourceHOnePullbacks318
set_option maxHeartbeats 700000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
local instance sourceIntegral : IsIntegral (ContactGlobalSmooth318.Model SourceTwistArithmetic318.units) :=
  ContactProjectiveModel318.model_integral SourceTwistArithmetic318.units
local instance characterFinite (i : Fin 4) : IsFinite (CompletedCharacterGlobal318.completedMap i) :=
  CompletedCharacterFinite318.completedMap_finite i
local instance fifthFinite : IsFinite FifthCompletedGlobal318.map := FifthCompletedFinite318.finite

/-- Actual direct-image/source cohomology equivalence for each of the four completed quotients. -/
@[expose] def characterEquivalence (i : Fin 4) :
    pushedH (CompletedCharacterGlobal318.completedMap i) 1 ≃+ SourceHOne :=
  AffineHOneComparison318.equivalence (CompletedCharacterGlobal318.completedMap i)

/-- The same original comparison for the fifth completed quotient, including infinity. -/
@[expose] def fifthEquivalence : pushedH FifthCompletedGlobal318.map 1 ≃+ SourceHOne :=
  AffineHOneComparison318.equivalence FifthCompletedGlobal318.map

theorem character_comparison (i : Fin 4) (x : pushedH (CompletedCharacterGlobal318.completedMap i) 1) :
    characterEquivalence i x = SchemeSourceCohomology318.comparison
      (CompletedCharacterGlobal318.completedMap i) 1 x := rfl

theorem fifth_comparison (x : pushedH FifthCompletedGlobal318.map 1) :
    fifthEquivalence x = SchemeSourceCohomology318.comparison FifthCompletedGlobal318.map 1 x := rfl

/-- Original trace/8 transported to genuine cohomology of the original common source. -/
@[expose] def characterTransfer (i : Fin 4) :
    SourceHOne →+ structureH (CompletedCharacterSchemeMaps318.Target i) 1 :=
  AffineHOneComparison318.transfer (CompletedCharacterGlobal318.completedMap i) (characterRetraction i)
@[expose] def fifthTransfer : SourceHOne →+ structureH FifthCompletedGlobal318.Target 1 :=
  AffineHOneComparison318.transfer FifthCompletedGlobal318.map fifthRetraction

theorem character_split (i : Fin 4) (x : structureH (CompletedCharacterSchemeMaps318.Target i) 1) :
    characterTransfer i (characterPullback i x) = x :=
  AffineHOneComparison318.transfer_pullback _ _
    (ActualQuotientSheafRetraction318.character_split i) x

theorem fifth_split (x : structureH FifthCompletedGlobal318.Target 1) :
    fifthTransfer (fifthPullback x) = x :=
  AffineHOneComparison318.transfer_pullback _ _ ActualQuotientSheafRetraction318.fifth_split x

theorem character_transfer_surjective (i : Fin 4) : Function.Surjective (characterTransfer i) :=
  Function.RightInverse.surjective (character_split i)
theorem fifth_transfer_surjective : Function.Surjective fifthTransfer :=
  Function.RightInverse.surjective fifth_split

@[expose] def characterProjection (i : Fin 4) : SourceHOne →+ SourceHOne :=
  (characterPullback i).comp (characterTransfer i)
@[expose] def fifthProjection : SourceHOne →+ SourceHOne := fifthPullback.comp fifthTransfer

theorem character_projection_twice (i : Fin 4) (x : SourceHOne) :
    characterProjection i (characterProjection i x) = characterProjection i x := by
  change characterPullback i (characterTransfer i (characterPullback i (characterTransfer i x))) = _
  rw [character_split]
  rfl

theorem fifth_projection_twice (x : SourceHOne) : fifthProjection (fifthProjection x) = fifthProjection x := by
  change fifthPullback (fifthTransfer (fifthPullback (fifthTransfer x))) = _
  rw [fifth_split]
  rfl

end ActualSourceHOneTransfers318
