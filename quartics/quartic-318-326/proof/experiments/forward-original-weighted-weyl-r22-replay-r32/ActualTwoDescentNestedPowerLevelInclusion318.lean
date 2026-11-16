module
public import ActualTwoDescentPrimaryInvolutionDetection318
public section
noncomputable section
namespace ActualTwoDescentNestedPowerLevelInclusion318
set_option maxHeartbeats 16000000

open ActualTwoDescentPrimaryPowerLevels318
variable (G : Type*) [CommGroup G]

def nestedLevelInclusion (N k : ℕ) : powerLevel (powerLevel G N) k →* powerLevel G k where
  toFun x := ⟨x.val.val,congrArg Subtype.val x.property⟩
  map_one' := rfl
  map_mul' x y := rfl

lemma actual_nested_level_injective (N k : ℕ) : Function.Injective (nestedLevelInclusion G N k) := by
  intro x y h; apply Subtype.ext; apply Subtype.ext
  exact congrArg Subtype.val h

end ActualTwoDescentNestedPowerLevelInclusion318
