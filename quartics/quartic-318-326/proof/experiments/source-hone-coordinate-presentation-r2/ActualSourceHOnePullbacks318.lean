module
public import SchemeSourceCohomology318
public import ActualQuotientHOne318

public section
noncomputable section
namespace ActualSourceHOnePullbacks318
open AlgebraicGeometry CategoryTheory
open SheafCohomologyRetraction318 ActualQuotientSheafRetraction318
set_option maxHeartbeats 600000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The actual source's H¹, shared by all five original completed maps. -/
abbrev SourceHOne := structureH (ContactGlobalSmooth318.Model SourceTwistArithmetic318.units) 1

@[expose] def characterPullback (i : Fin 4) :
    structureH (CompletedCharacterSchemeMaps318.Target i) 1 →+ SourceHOne :=
  SchemeSourceCohomology318.pullback (CompletedCharacterGlobal318.completedMap i) 1

@[expose] def fifthPullback : structureH FifthCompletedGlobal318.Target 1 →+ SourceHOne :=
  SchemeSourceCohomology318.pullback FifthCompletedGlobal318.map 1

theorem character_injective (i : Fin 4) : Function.Injective (characterPullback i) :=
  SchemeSourceCohomology318.pullback_one_injective_of_retraction _
    (characterRetraction i) (character_split i)

theorem fifth_injective : Function.Injective fifthPullback :=
  SchemeSourceCohomology318.pullback_one_injective_of_retraction _ fifthRetraction fifth_split

theorem character_factorization (i : Fin 4)
    (x : structureH (CompletedCharacterSchemeMaps318.Target i) 1) :
    characterPullback i x = SchemeSourceCohomology318.comparison
      (CompletedCharacterGlobal318.completedMap i) 1 (ActualQuotientHOne318.characterPullback i 1 x) := rfl

theorem fifth_factorization (x : structureH FifthCompletedGlobal318.Target 1) :
    fifthPullback x = SchemeSourceCohomology318.comparison FifthCompletedGlobal318.map 1
      (ActualQuotientHOne318.fifthPullback 1 x) := rfl

end ActualSourceHOnePullbacks318
