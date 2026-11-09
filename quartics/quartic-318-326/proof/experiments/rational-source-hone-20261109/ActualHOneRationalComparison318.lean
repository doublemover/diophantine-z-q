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
local instance sourceComparisonInstance : Module ℚ SourceHOne := sourceModule

/-- Rational linearity uses the proved structural module actions and the uniqueness of rational division. -/
@[expose] def characterComparison (i : Fin 4) :
    letI := characterPushedModule i
    pushedH (CompletedCharacterGlobal318.completedMap i) 1 ≃ₗ[ℚ] SourceHOne :=
  letI := characterPushedModule i
  @RationalAdditiveEquivalence318.equivalence
    (pushedH (CompletedCharacterGlobal318.completedMap i) 1) SourceHOne inferInstance inferInstance
    (characterPushedModule i) sourceModule (ActualSourceHOneTransfers318.characterEquivalence i)
@[expose] def fifthComparison : letI := fifthPushedModule
    pushedH FifthCompletedGlobal318.map 1 ≃ₗ[ℚ] SourceHOne :=
  letI := fifthPushedModule
  @RationalAdditiveEquivalence318.equivalence
    (pushedH FifthCompletedGlobal318.map 1) SourceHOne inferInstance inferInstance
    fifthPushedModule sourceModule ActualSourceHOneTransfers318.fifthEquivalence

theorem character_comparison_original (i : Fin 4) (x : pushedH (CompletedCharacterGlobal318.completedMap i) 1) :
    characterComparison i x = SchemeSourceCohomology318.comparison (CompletedCharacterGlobal318.completedMap i) 1 x := rfl

theorem fifth_comparison_original (x : pushedH FifthCompletedGlobal318.map 1) :
    fifthComparison x = SchemeSourceCohomology318.comparison FifthCompletedGlobal318.map 1 x := rfl

end ActualHOneRational318
