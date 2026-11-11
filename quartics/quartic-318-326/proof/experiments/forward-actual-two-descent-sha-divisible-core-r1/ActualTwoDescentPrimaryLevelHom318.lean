module
public import ActualTwoDescentInfinitePrimarySharpLevels318
public section
noncomputable section
namespace ActualTwoDescentPrimaryLevelHom318
set_option maxHeartbeats 16000000

open ActualTwoDescentPrimaryPowerLevels318
variable {G H : Type*} [CommGroup G] [CommGroup H]

def powerLevelMap (f : G →* H) (k : ℕ) : powerLevel G k →* powerLevel H k where
  toFun x := ⟨f x,by rw [←map_pow,x.property,map_one]⟩
  map_one' := Subtype.ext (map_one f)
  map_mul' x y := Subtype.ext (map_mul f x y)

lemma actual_power_level_map_injective (f : G →* H) (hf : Function.Injective f) (k : ℕ) :
    Function.Injective (powerLevelMap f k) := by
  intro x y h; apply Subtype.ext
  exact hf (congrArg Subtype.val h)

end ActualTwoDescentPrimaryLevelHom318
