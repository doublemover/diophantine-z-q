module
public import ActualTwoDescentPrimaryLevelHom318
public section
noncomputable section
namespace ActualTwoDescentPrimaryEmbeddingSurjective318
set_option maxHeartbeats 16000000

open ActualTwoDescentPrimaryPowerLevels318 ActualTwoDescentFinitePowerLevels318
open ActualTwoDescentInfinitePrimarySharpLevels318 ActualTwoDescentPrimaryLevelHom318
variable {G H : Type*} [CommGroup G] [CommGroup H] [Infinite G] [Infinite H]

/-- An injective homomorphism between two infinite rank-one primary groups is surjective on every actual power level, hence globally. -/
lemma actual_primary_embedding_surjective (hG : IsPGroup 2 G) (hH : IsPGroup 2 H)
    (ftG : Finite (powerLevel G 1)) (ftH : Finite (powerLevel H 1))
    (hcG : Nat.card (powerLevel G 1) ≤ 2) (hcH : Nat.card (powerLevel H 1) ≤ 2)
    (f : G →* H) (hf : Function.Injective f) : Function.Surjective f := by
  intro y
  obtain ⟨k,hk⟩ := isPGroup_iff_pow_pow_eq_one.mp hH y
  letI := actual_power_levels_finite H ftH k
  have he : Nat.card (powerLevel G k)=Nat.card (powerLevel H k) :=
    (actual_infinite_primary_level_card G hG ftG hcG k).trans (actual_infinite_primary_level_card H hH ftH hcH k).symm
  have hs := ((Nat.bijective_iff_injective_and_card (powerLevelMap f k)).mpr
    ⟨actual_power_level_map_injective f hf k,he⟩).surjective
  obtain ⟨x,hx⟩ := hs ⟨y,hk⟩
  exact ⟨x.val,congrArg Subtype.val hx⟩

end ActualTwoDescentPrimaryEmbeddingSurjective318
