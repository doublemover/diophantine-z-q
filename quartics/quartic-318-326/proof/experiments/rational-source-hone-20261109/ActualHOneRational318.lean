module
public import ActualHOneRationalComparison318
public import ActualHOneRationalPullbacks318
public import ActualSourceHOneTransfers318
public import RationalAdditiveEquivalence318

public section
noncomputable section
namespace ActualHOneRational318
open AlgebraicGeometry CategoryTheory SourceTwistArithmetic318
open SheafCohomologyRetraction318 ActualSourceHOnePullbacks318
set_option maxHeartbeats 700000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
local instance sourceTransferInstance : Module ℚ SourceHOne := sourceModule

@[expose] def characterTransfer (i : Fin 4) : letI := characterModule i
    SourceHOne →ₗ[ℚ] structureH (CompletedCharacterSchemeMaps318.Target i) 1 :=
  letI := characterModule i
  @AddMonoidHom.toRatLinearMap
    SourceHOne (structureH (CompletedCharacterSchemeMaps318.Target i) 1)
    inferInstance sourceModule inferInstance (characterModule i)
    (ActualSourceHOneTransfers318.characterTransfer i)
@[expose] def fifthTransfer : letI := fifthModule
    SourceHOne →ₗ[ℚ] structureH FifthCompletedGlobal318.Target 1 :=
  letI := fifthModule
  @AddMonoidHom.toRatLinearMap
    SourceHOne (structureH FifthCompletedGlobal318.Target 1)
    inferInstance sourceModule inferInstance fifthModule ActualSourceHOneTransfers318.fifthTransfer

theorem character_split (i : Fin 4) (x : structureH (CompletedCharacterSchemeMaps318.Target i) 1) :
    characterTransfer i (characterPullback i x) = x := ActualSourceHOneTransfers318.character_split i x

theorem fifth_split (x : structureH FifthCompletedGlobal318.Target 1) :
    fifthTransfer (fifthPullback x) = x := ActualSourceHOneTransfers318.fifth_split x

end ActualHOneRational318
