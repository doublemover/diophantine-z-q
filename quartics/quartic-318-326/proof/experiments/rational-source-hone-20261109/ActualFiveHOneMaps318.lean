module
public import ActualHOneRational318
public import Mathlib.LinearAlgebra.Pi

public section
noncomputable section
namespace ActualFiveHOneMaps318
open SheafCohomologyRetraction318 ActualSourceHOnePullbacks318
set_option maxHeartbeats 700000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

local instance sourceInstance : Module ℚ SourceHOne := ActualHOneRational318.sourceModule

/-- Four complementary quotient targets and the original fifth target, without changing carriers. -/
abbrev TargetHOne : Option (Fin 4) → Type
  | none => structureH FifthCompletedGlobal318.Target 1
  | some i => structureH (CompletedCharacterSchemeMaps318.Target i) 1
instance (i : Option (Fin 4)) : AddCommGroup (TargetHOne i) := by cases i <;> exact inferInstance
instance (i : Option (Fin 4)) : Module ℚ (TargetHOne i) := by
  cases i with
  | none => exact ActualHOneRational318.fifthModule
  | some i => exact ActualHOneRational318.characterModule i

@[expose] def pullback : (i : Option (Fin 4)) → TargetHOne i →ₗ[ℚ] SourceHOne
  | none => ActualHOneRational318.fifthPullback
  | some i => ActualHOneRational318.characterPullback i
@[expose] def transfer : (i : Option (Fin 4)) → SourceHOne →ₗ[ℚ] TargetHOne i
  | none => ActualHOneRational318.fifthTransfer
  | some i => ActualHOneRational318.characterTransfer i

theorem split (i : Option (Fin 4)) (x : TargetHOne i) : transfer i (pullback i x) = x := by
  cases i with
  | none => exact ActualHOneRational318.fifth_split x
  | some i => exact ActualHOneRational318.character_split i x

theorem pullback_injective (i : Option (Fin 4)) : Function.Injective (pullback i) :=
  Function.LeftInverse.injective (split i)
theorem transfer_surjective (i : Option (Fin 4)) : Function.Surjective (transfer i) :=
  Function.RightInverse.surjective (split i)

/-- The actual sum of all five original H1 pullbacks, now a structural Q-linear map. -/
@[expose] def sumPullback : ((i : Option (Fin 4)) → TargetHOne i) →ₗ[ℚ] SourceHOne :=
  ∑ i, (pullback i).comp (LinearMap.proj i)
/-- All five normalized source transfers, simultaneously and with their original components. -/
@[expose] def allTransfers : SourceHOne →ₗ[ℚ] ((i : Option (Fin 4)) → TargetHOne i) :=
  LinearMap.pi transfer

theorem sumPullback_apply (x : (i : Option (Fin 4)) → TargetHOne i) :
    sumPullback x = ∑ i, pullback i (x i) := by simp [sumPullback]
theorem allTransfers_apply (x : SourceHOne) (i : Option (Fin 4)) :
    allTransfers x i = transfer i x := rfl

theorem sumPullback_single (i : Option (Fin 4)) (x : TargetHOne i) :
    sumPullback (Pi.single i x) = pullback i x := by
  classical
  simp [sumPullback,Pi.single_apply]

theorem split_single (i : Option (Fin 4)) (x : TargetHOne i) :
    allTransfers (sumPullback (Pi.single i x)) i = x := by
  rw [sumPullback_single,allTransfers_apply,split]

/-- Each actual normalized source projection is an idempotent Q-linear endomorphism. -/
@[expose] def projection (i : Option (Fin 4)) : SourceHOne →ₗ[ℚ] SourceHOne :=
  (pullback i).comp (transfer i)
theorem projection_twice (i : Option (Fin 4)) (x : SourceHOne) :
    projection i (projection i x) = projection i x := by
  change pullback i (transfer i (pullback i (transfer i x))) = _
  rw [split]
  rfl

end ActualFiveHOneMaps318
