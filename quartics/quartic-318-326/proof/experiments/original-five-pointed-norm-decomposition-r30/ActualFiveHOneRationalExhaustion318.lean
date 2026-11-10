module
public import ActualSourceHOneRationalSpanning318
public import ActualFiveHOneDecomposition318

public section
noncomputable section
namespace ActualFiveHOneRationalExhaustion318
open ActualFiveHOneDecomposition318 ActualSourceHOneRationalSpanning318
open ActualSourceHOnePullbacks318
open scoped BigOperators
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Structural rational actions on the same five original target cohomology groups. -/
instance targetRationalModule (i : Index) : Module ℚ (TargetHOne i) := by
  cases i with
  | none => exact ActualHOneRational318.fifthModule
  | some i => exact ActualHOneRational318.characterModule i

@[expose] def pullbackLinear (i : Index) : TargetHOne i →ₗ[ℚ] SourceHOne :=
  (pullback i).toRatLinearMap
@[expose] def transferLinear (i : Index) : SourceHOne →ₗ[ℚ] TargetHOne i :=
  (transfer i).toRatLinearMap
@[expose] def sumLinear : ((i : Index) → TargetHOne i) →ₗ[ℚ] SourceHOne :=
  sumPullback.toRatLinearMap
@[expose] def transfersLinear : SourceHOne →ₗ[ℚ] ((i : Index) → TargetHOne i) :=
  allTransfers.toRatLinearMap

theorem splitLinear (i : Index) (x : TargetHOne i) :
    transferLinear i (pullbackLinear i x) = x := split i x

/-- Individual genuine splittings already make all five targets finite-dimensional. -/
instance targetFiniteDimensional (i : Index) : FiniteDimensional ℚ (TargetHOne i) :=
  FiniteDimensional.of_injective (pullbackLinear i)
    (Function.LeftInverse.injective (splitLinear i))

/-- Exact remaining geometric nonvanishing input, not assumed from a curve label. -/
@[expose] def TargetsNonzero : Prop := ∀ i : Index, ∃ x : TargetHOne i, x ≠ 0

theorem target_product_finrank_ge_five (hnonzero : TargetsNonzero) :
    5 ≤ Module.finrank ℚ ((i : Index) → TargetHOne i) := by
  rw [Module.finrank_pi_fintype]
  calc
    5 = ∑ _i : Index, 1 := by decide
    _ ≤ ∑ i : Index, Module.finrank ℚ (TargetHOne i) := by
      apply Finset.sum_le_sum
      intro i _
      exact Nat.succ_le_of_lt (Module.finrank_pos_iff_exists_ne_zero.mpr (hnonzero i))

theorem sumLinear_injective (hcross : CrossTermsVanish) : Function.Injective sumLinear :=
  FiniteSplitTransfer318.sumPullback_injective pullback transfer split hcross

/-- The concrete upper bound removes the formerly separate common-kernel
hypothesis once actual cross terms and target nonvanishing have been proved. -/
theorem sumLinear_surjective (hcross : CrossTermsVanish) (hnonzero : TargetsNonzero) :
    Function.Surjective sumLinear := by
  have hinj := sumLinear_injective hcross
  have hle := LinearMap.finrank_le_finrank_of_injective hinj
  have hlower := target_product_finrank_ge_five hnonzero
  have hupper : Module.finrank ℚ SourceHOne ≤ 5 := source_finrank_le_five
  have heq : Module.finrank ℚ ((i : Index) → TargetHOne i) = Module.finrank ℚ SourceHOne := by
    omega
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank heq).mp hinj

theorem source_finrank_eq_five (hcross : CrossTermsVanish) (hnonzero : TargetsNonzero) :
    Module.finrank ℚ SourceHOne = 5 := by
  have hle := LinearMap.finrank_le_finrank_of_injective (sumLinear_injective hcross)
  have hlower := target_product_finrank_ge_five hnonzero
  have hupper : Module.finrank ℚ SourceHOne ≤ 5 := source_finrank_le_five
  omega

/-- The original common transfer kernel is zero, derived rather than assumed. -/
theorem jointly_detect_zero (hcross : CrossTermsVanish) (hnonzero : TargetsNonzero) :
    JointlyDetectZero :=
  (sumPullback_surjective_iff hcross).mp (sumLinear_surjective hcross hnonzero)

/-- Conditional only on the two explicitly displayed geometric inputs: an
actual rational equivalence whose forward and inverse are the original maps. -/
@[expose] def actualEquivalence (hcross : CrossTermsVanish) (hnonzero : TargetsNonzero) :
    ((i : Index) → TargetHOne i) ≃ₗ[ℚ] SourceHOne :=
  LinearEquiv.ofBijective sumLinear
    ⟨sumLinear_injective hcross,sumLinear_surjective hcross hnonzero⟩

theorem actualEquivalence_apply (hcross : CrossTermsVanish) (hnonzero : TargetsNonzero)
    (x : (i : Index) → TargetHOne i) :
    actualEquivalence hcross hnonzero x = sumPullback x := rfl

theorem actualEquivalence_symm (hcross : CrossTermsVanish) (hnonzero : TargetsNonzero)
    (x : SourceHOne) : (actualEquivalence hcross hnonzero).symm x = allTransfers x := by
  have h := FiniteSplitTransfer318.transfer_sum pullback transfer split hcross
    ((actualEquivalence hcross hnonzero).symm x)
  change allTransfers ((actualEquivalence hcross hnonzero)
    ((actualEquivalence hcross hnonzero).symm x)) = _ at h
  rw [LinearEquiv.apply_symm_apply] at h
  exact h.symm

end ActualFiveHOneRationalExhaustion318
