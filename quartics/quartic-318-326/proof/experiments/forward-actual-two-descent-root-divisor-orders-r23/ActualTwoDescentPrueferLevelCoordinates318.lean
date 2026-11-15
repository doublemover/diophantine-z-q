module
public import ActualTwoDescentAdditivePrimaryLevels318
public section
noncomputable section
namespace ActualTwoDescentPrueferLevelCoordinates318
set_option maxHeartbeats 16000000
open ActualTwoDescentDyadicPrueferModel318 ActualTwoDescentDyadicPrueferInvolutions318
open ActualTwoDescentPrimaryPowerLevels318 ActualTwoDescentFinitePowerLevels318
open ActualTwoDescentPowerLevelCyclic318 ActualTwoDescentInfinitePrimarySharpLevels318
open ActualTwoDescentAdditivePrimaryLevels318

abbrev PrueferAdd := Additive PrueferTwo
abbrev PrueferLevel (k : ℕ) := additivePowerLevel PrueferAdd k

lemma actual_pruefer_level_finite (k : ℕ) : Finite (PrueferLevel k) := by
  letI := actual_power_levels_finite PrueferTwo actual_pruefer_two_finite k
  exact Finite.of_equiv (Additive (powerLevel PrueferTwo k)) (additivePowerLevelEquiv PrueferAdd k).symm.toEquiv

lemma actual_pruefer_level_card (k : ℕ) : Nat.card (PrueferLevel k)=2^k := by
  letI := actual_pruefer_infinite
  rw [Nat.card_congr (additivePowerLevelEquiv PrueferAdd k).toEquiv]
  exact actual_infinite_primary_level_card PrueferTwo actual_pruefer_is_two_group
    actual_pruefer_two_finite actual_pruefer_two_card k

lemma actual_pruefer_level_cyclic (k : ℕ) : IsAddCyclic (PrueferLevel k) := by
  letI := actual_power_level_cyclic PrueferTwo actual_pruefer_two_finite actual_pruefer_two_card k
  let e := additivePowerLevelEquiv PrueferAdd k
  exact isAddCyclic_of_surjective e.symm.toAddMonoidHom e.symm.surjective

/-- Any actual cyclic coordinate is allowed; endomorphism scalars will be
proved intrinsic and compatible before taking a2-adic limit. -/
def prueferLevelCoordinate (k : ℕ) : ZMod (2^k) ≃+ PrueferLevel k := by
  simpa only [actual_pruefer_level_card] using
    (zmodAddCyclicAddEquiv (actual_pruefer_level_cyclic k))

end ActualTwoDescentPrueferLevelCoordinates318
