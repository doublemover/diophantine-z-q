module
public import ActualTwoDescentFiniteTorsionStabilization318
public section
noncomputable section
namespace ActualTwoDescentTrivialShaPowerCard318
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

open ActualTwoDescentActualShaPrimary318 ActualTwoDescentActualShaPower318 ActualTwoDescentActualShaPowerBounds318
open ActualTwoDescentPrimaryPowerLevels318

lemma actual_trivial_sha_power_card (n : ℚ) (hn : n ≠ 0)
    (hz : Subsingleton (actualShaPrimary n hn)) (k : ℕ) : Nat.card (actualShaPower n hn k)=1 := by
  letI := hz
  rw [actual_sha_power_card]
  exact Nat.card_eq_one_iff_unique.mpr ⟨inferInstance,inferInstance⟩

end ActualTwoDescentTrivialShaPowerCard318
