module
public import ActualTwoDescentPowerLevelCyclic318
public section
noncomputable section
namespace ActualTwoDescentFinitePrimaryImages318
set_option maxHeartbeats 16000000

open ActualTwoDescentPrimaryPowerLevels318 ActualTwoDescentFinitePowerLevels318 ActualTwoDescentPowerLevelCyclic318
variable {G H : Type*} [CommGroup G] [CommGroup H]

/-- Every finite image of a primary group is already covered by one actual power level. -/
lemma actual_finite_image_one_level [Finite H] (hP : IsPGroup 2 G) (f : G →* H) (hf : Function.Surjective f) :
    ∃ k, Function.Surjective (f.comp (powerLevel G k).subtype) := by
  classical
  letI := Fintype.ofFinite H
  let s : H → G := fun h => Classical.choose (hf h)
  have hs (h : H) : f (s h)=h := Classical.choose_spec (hf h)
  have ht (h : H) : ∃ k, (s h)^(2^k)=1 := (isPGroup_iff_pow_pow_eq_one.mp hP) (s h)
  let a : H → ℕ := fun h => Classical.choose (ht h)
  let N := Finset.univ.sup a
  refine ⟨N,?_⟩
  intro h
  have hle : a h ≤ N := Finset.le_sup (Finset.mem_univ h)
  have hm : s h ∈ powerLevel G N := actual_power_level_mono G hle (Classical.choose_spec (ht h))
  exact ⟨⟨s h,hm⟩,hs h⟩

lemma actual_finite_primary_image_cyclic [Finite H] (hP : IsPGroup 2 G)
    (ht : Finite (powerLevel G 1)) (hc : Nat.card (powerLevel G 1) ≤ 2)
    (f : G →* H) (hf : Function.Surjective f) : IsCyclic H := by
  obtain ⟨k,hk⟩ := actual_finite_image_one_level hP f hf
  letI := actual_power_level_cyclic G ht hc k
  exact isCyclic_of_surjective (f.comp (powerLevel G k).subtype) hk

end ActualTwoDescentFinitePrimaryImages318
