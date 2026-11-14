module
public import ActualTwoDescentPrimaryShaPowerEquivalence318
public section
noncomputable section
namespace ActualTwoDescentActualShaPowerBounds318
set_option maxHeartbeats 16000000
variable {F : Type} [Field F] [CharZero F] [DecidableEq F]
local notation "Qbar" => AlgebraicClosure F
local notation "Gal" => Field.absoluteGaloisGroup F
local instance : DecidableEq Qbar := Classical.decEq _
open ActualTwoDescentEllipticModel318 ActualTwoDescentFieldAlgebraicClosureHalving318
open ActualTwoDescentFieldGaloisPointAction318 ActualTwoDescentFieldGaloisFixedRational318
open ActualTwoDescentFieldHalvingCocycle318 ActualTwoDescentContinuousEllipticCocycles318
open ActualTwoDescentFullEllipticRepresentation318 ActualTwoDescentFullEllipticHOneKernel318
open groupCohomology
open ActualTwoDescentPowerValuedCocycles318 ActualTwoDescentPowerTorsionBoundaries318
open ActualTwoDescentHigherKummerHom318 ActualTwoDescentHigherFullClassMap318 ActualTwoDescentHigherFullKernel318
open ActualTwoDescentHigherFullLifting318 ActualTwoDescentGeometricPowerTorsion318
open ActualTwoDescentFullCocycleRestriction318 ActualTwoDescentGeometricPointTransport318
open ActualTwoDescentSquareClassFieldMap318
variable {L : Type} [Field L] [CharZero L] [DecidableEq L]
local instance : DecidableEq (AlgebraicClosure L) := Classical.decEq _
local instance (p : ℕ) [Fact p.Prime] : DecidableEq (ℚ_[p]) := Classical.decEq _

open ActualTwoDescentActualShaPower318 ActualTwoDescentActualShaPrimary318 ActualTwoDescentPrimaryShaPowerEquivalence318
open ActualTwoDescentPrimaryPowerLevels318 ActualTwoDescentFinitePowerLevels318 ActualTwoDescentPowerLevelCyclic318
open ActualTwoDescentActualShaReducedPrimary318 ActualTwoDescentInfinitePrimarySharpLevels318
open ActualTwoDescentEllipticDoubleQuotient318 ActualTwoDescentAllPlacesIntersection318

lemma actual_sha_power_card (n : ℚ) (hn : n ≠ 0) (k : ℕ) :
    Nat.card (actualShaPower n hn k)=Nat.card (powerLevel (actualShaPrimary n hn) k) :=
  (Nat.card_congr (primaryShaPowerEquiv n hn k).toEquiv).symm

/-- Actual higher Sha torsion is finite with the proved power bound. -/
theorem actual_sha_power_finite_bound (n : ℚ) (hn : n ≠ 0)
    (hf : Finite (DoubleQuotient n)) (hb : Nat.card (DoubleQuotient n) ≤ 8)
    (hS : Nat.card (allPlacesImage n hn)=8) (k : ℕ) :
    Finite (actualShaPower n hn k) ∧ Nat.card (actualShaPower n hn k) ≤ 2^k := by
  obtain ⟨ht,hc⟩ := actual_sha_primary_level_bounds n hn hf hb hS
  letI := actual_power_levels_finite (actualShaPrimary n hn) ht k
  have hfin : Finite (Multiplicative (actualShaPower n hn k)) :=
    Finite.of_equiv _ (primaryShaPowerEquiv n hn k).toEquiv
  exact ⟨hfin,by rw [actual_sha_power_card]; exact actual_power_levels_card _ ht hc k⟩

lemma actual_infinite_sha_power_card (n : ℚ) (hn : n ≠ 0)
    (hf : Finite (DoubleQuotient n)) (hb : Nat.card (DoubleQuotient n) ≤ 8)
    (hS : Nat.card (allPlacesImage n hn)=8) [Infinite (actualShaPrimary n hn)] (k : ℕ) :
    Nat.card (actualShaPower n hn k)=2^k := by
  obtain ⟨ht,hc⟩ := actual_sha_primary_level_bounds n hn hf hb hS
  rw [actual_sha_power_card]
  exact actual_infinite_primary_level_card _ (actual_sha_primary_is_two_group n hn) ht hc k

end ActualTwoDescentActualShaPowerBounds318
