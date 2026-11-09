module
public import ActualHOneRationalStructures318
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
local instance sourcePullbacksInstance : Module ℚ SourceHOne := sourceModule

@[expose] def characterPullback (i : Fin 4) : letI := characterModule i
    structureH (CompletedCharacterSchemeMaps318.Target i) 1 →ₗ[ℚ] SourceHOne :=
  letI := characterModule i
  @AddMonoidHom.toRatLinearMap
    (structureH (CompletedCharacterSchemeMaps318.Target i) 1) SourceHOne
    inferInstance (characterModule i) inferInstance sourceModule
    (ActualSourceHOnePullbacks318.characterPullback i)
@[expose] def fifthPullback : letI := fifthModule
    structureH FifthCompletedGlobal318.Target 1 →ₗ[ℚ] SourceHOne :=
  letI := fifthModule
  @AddMonoidHom.toRatLinearMap
    (structureH FifthCompletedGlobal318.Target 1) SourceHOne
    inferInstance fifthModule inferInstance sourceModule ActualSourceHOnePullbacks318.fifthPullback
end ActualHOneRational318
