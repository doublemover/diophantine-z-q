module
public import ActualTwoDescentPrimaryEmbeddingSurjective318
public section
noncomputable section
namespace ActualTwoDescentRankOnePrimaryEquivalence318
set_option maxHeartbeats 16000000

open ActualTwoDescentPrimaryPowerLevels318 ActualTwoDescentFinitePowerLevels318 ActualTwoDescentPowerLevelCyclic318
open ActualTwoDescentInfinitePrimaryDivisible318 ActualTwoDescentInfinitePrimarySharpLevels318
open ActualTwoDescentPrimaryBaerExtension318 ActualTwoDescentPrimaryInvolutionDetection318
open ActualTwoDescentPrimaryEmbeddingSurjective318
variable {G H : Type} [CommGroup G] [CommGroup H] [Infinite G] [Infinite H]

/-- Complete abstract rank-one primary classification: actual compatible extension from involutions gives an isomorphism, with no cofinite-structure theorem assumed. -/
theorem actual_rank_one_primary_equivalence (hG : IsPGroup 2 G) (hH : IsPGroup 2 H)
    (ftG : Finite (powerLevel G 1)) (ftH : Finite (powerLevel H 1))
    (hcG : Nat.card (powerLevel G 1) ≤ 2) (hcH : Nat.card (powerLevel H 1) ≤ 2) : Nonempty (G ≃* H) := by
  letI := ftG
  letI := ftH
  letI := actual_power_level_cyclic G ftG hcG 1
  letI := actual_power_level_cyclic H ftH hcH 1
  have he : Nat.card (powerLevel G 1)=Nat.card (powerLevel H 1) :=
    (actual_infinite_primary_level_card G hG ftG hcG 1).trans (actual_infinite_primary_level_card H hH ftH hcH 1).symm
  let e : powerLevel G 1 ≃* powerLevel H 1 := mulEquivOfCyclicCardEq he
  let g : powerLevel G 1 →* H := (powerLevel H 1).subtype.comp e.toMonoidHom
  obtain ⟨f,hf⟩ := actual_primary_hom_extension hH (actual_infinite_primary_square_surjective H hH ftH hcH)
    (powerLevel G 1).subtype Subtype.val_injective g
  have hi : Function.Injective f := by
    apply actual_primary_injective_of_involution_injective hG f
    intro x hx hfx
    let X : powerLevel G 1 := ⟨x,by simpa only [pow_one] using hx⟩
    have heX : e X=1 := by
      apply Subtype.ext
      exact (hf X).symm.trans hfx
    have hX : X=1 := e.injective (heX.trans e.map_one.symm)
    exact congrArg Subtype.val hX
  exact ⟨MulEquiv.ofBijective f ⟨hi,actual_primary_embedding_surjective hG hH ftG ftH hcG hcH f hi⟩⟩

end ActualTwoDescentRankOnePrimaryEquivalence318
