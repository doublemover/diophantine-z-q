module
public import ActualTwoDescentPrimaryPowerLevels318
public section
noncomputable section
namespace ActualTwoDescentFinitePowerLevels318
set_option maxHeartbeats 16000000

open ActualTwoDescentPrimaryPowerLevels318 ActualTwoDescentFiniteHomFibers318
variable (G : Type*) [CommGroup G]

lemma actual_power_zero_subsingleton : Subsingleton (powerLevel G 0) := by
  constructor
  intro x y
  apply Subtype.ext
  have hx : x.val=1 := by simpa only [pow_zero,pow_one] using x.property
  have hy : y.val=1 := by simpa only [pow_zero,pow_one] using y.property
  exact hx.trans hy.symm

/-- Finite2-torsion implies finiteness at EVERY higher2-power level, without assuming the full primary group finite. -/
lemma actual_power_levels_finite (hfinite : Finite (powerLevel G 1)) : ∀ k, Finite (powerLevel G k) := by
  letI := hfinite
  intro k
  induction k with
  | zero => letI := actual_power_zero_subsingleton G; infer_instance
  | succ k ih =>
    letI := ih
    letI : Finite (squareLevel G k).ker := Finite.of_injective (squareKernelInclusion G k) (actual_square_kernel_injective G k)
    exact actual_finite_of_finite_kernel_target (squareLevel G k)

/-- At most two2-torsion elements give the sharp bound2^k on each actual higher torsion level. -/
lemma actual_power_levels_card (hfinite : Finite (powerLevel G 1)) (hcard : Nat.card (powerLevel G 1) ≤ 2) :
    ∀ k, Nat.card (powerLevel G k) ≤ 2^k := by
  letI := hfinite
  intro k
  induction k with
  | zero =>
    letI := actual_power_zero_subsingleton G
    have hi : Function.Injective (fun _ : powerLevel G 0 => (0 : Fin 1)) := fun _ _ _ => Subsingleton.elim _ _
    simpa using Nat.card_le_card_of_injective _ hi
  | succ k ih =>
    letI := actual_power_levels_finite G hfinite k
    letI : Finite (squareLevel G k).ker := Finite.of_injective (squareKernelInclusion G k) (actual_square_kernel_injective G k)
    have hk : Nat.card (squareLevel G k).ker ≤ 2 :=
      (Nat.card_le_card_of_injective (squareKernelInclusion G k) (actual_square_kernel_injective G k)).trans hcard
    calc
      _ ≤ Nat.card (powerLevel G k)*Nat.card (squareLevel G k).ker := actual_card_le_kernel_target (squareLevel G k)
      _ ≤ 2^k*2 := Nat.mul_le_mul ih hk
      _ = 2^(k+1) := (pow_succ 2 k).symm

end ActualTwoDescentFinitePowerLevels318
