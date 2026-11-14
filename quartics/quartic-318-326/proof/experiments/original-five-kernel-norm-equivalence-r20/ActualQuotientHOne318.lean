module
public import ActualQuotientSheafRetraction318
public import SheafCohomologyRetraction318

public section
noncomputable section
namespace ActualQuotientHOne318
open AlgebraicGeometry CategoryTheory
open ActualQuotientSheafRetraction318 SheafCohomologyRetraction318
set_option maxHeartbeats 600000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Actual cohomology pullback into the direct-image structure sheaf, for all four maps. -/
@[expose] def characterPullback (i : Fin 4) (n : ℕ) :=
  SheafCohomologyRetraction318.pullback (CompletedCharacterGlobal318.completedMap i) n
@[expose] def characterTransfer (i : Fin 4) (n : ℕ) :=
  SheafCohomologyRetraction318.transfer (CompletedCharacterGlobal318.completedMap i)
    (characterRetraction i) n
@[expose] def fifthPullback (n : ℕ) :=
  SheafCohomologyRetraction318.pullback FifthCompletedGlobal318.map n
@[expose] def fifthTransfer (n : ℕ) :=
  SheafCohomologyRetraction318.transfer FifthCompletedGlobal318.map fifthRetraction n

theorem character_split_all (i : Fin 4) (n : ℕ)
    (x : structureH (CompletedCharacterSchemeMaps318.Target i) n) :
    characterTransfer i n (characterPullback i n x) = x :=
  transfer_pullback _ _ (character_split i) n x

theorem fifth_split_all (n : ℕ) (x : structureH FifthCompletedGlobal318.Target n) :
    fifthTransfer n (fifthPullback n x) = x :=
  transfer_pullback _ _ fifth_split n x

/-- Genuine H^1 split injectivity for each of the four completed quotient maps. -/
theorem character_h1_injective (i : Fin 4) : Function.Injective (characterPullback i 1) :=
  Function.LeftInverse.injective (character_split_all i 1)

/-- Genuine H^1 split injectivity for the original fifth completed quotient map. -/
theorem fifth_h1_injective : Function.Injective (fifthPullback 1) :=
  Function.LeftInverse.injective (fifth_split_all 1)

theorem character_h1_transfer_surjective (i : Fin 4) :
    Function.Surjective (characterTransfer i 1) := Function.RightInverse.surjective (character_split_all i 1)

theorem fifth_h1_transfer_surjective : Function.Surjective (fifthTransfer 1) :=
  Function.RightInverse.surjective (fifth_split_all 1)

end ActualQuotientHOne318
