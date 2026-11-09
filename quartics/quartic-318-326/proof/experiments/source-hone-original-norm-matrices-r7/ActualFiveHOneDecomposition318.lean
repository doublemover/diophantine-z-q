module
public import ActualSourceHOneTransfers318
public import FiniteSplitTransfer318

public section
noncomputable section
namespace ActualFiveHOneDecomposition318
open SheafCohomologyRetraction318 ActualSourceHOnePullbacks318
open scoped BigOperators
set_option maxHeartbeats 700000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

abbrev Index := Option (Fin 4)

/-- All five unchanged target H1 groups, not differential or tangent substitutes. -/
abbrev TargetHOne : Index → Type
  | none => structureH FifthCompletedGlobal318.Target 1
  | some i => structureH (CompletedCharacterSchemeMaps318.Target i) 1

instance targetAddCommGroup (i : Index) : AddCommGroup (TargetHOne i) := by
  cases i <;> exact inferInstance

@[expose] def pullback : (i : Index) → TargetHOne i →+ SourceHOne
  | none => ActualSourceHOnePullbacks318.fifthPullback
  | some i => ActualSourceHOnePullbacks318.characterPullback i

@[expose] def transfer : (i : Index) → SourceHOne →+ TargetHOne i
  | none => ActualSourceHOneTransfers318.fifthTransfer
  | some i => ActualSourceHOneTransfers318.characterTransfer i

theorem split (i : Index) (x : TargetHOne i) : transfer i (pullback i x) = x := by
  cases i with
  | none => exact ActualSourceHOneTransfers318.fifth_split x
  | some i => exact ActualSourceHOneTransfers318.character_split i x

/-- Unconditional decomposition of actual source H1 for each original quotient. -/
@[expose] def quotientDecomposition (i : Index) :
    SourceHOne ≃+ (TargetHOne i × (transfer i).ker) :=
  SplitAdditiveRetraction318.equivalence (pullback i) (transfer i) (split i)

theorem quotientDecomposition_first (i : Index) (x : SourceHOne) :
    (quotientDecomposition i x).1 = transfer i x := rfl

theorem quotientDecomposition_second (i : Index) (x : SourceHOne) :
    ((quotientDecomposition i x).2 : SourceHOne) = x - pullback i (transfer i x) := rfl

theorem quotientDecomposition_symm (i : Index) (z : TargetHOne i × (transfer i).ker) :
    (quotientDecomposition i).symm z = pullback i z.1 + z.2.val := rfl

@[expose] def sumPullback : ((i : Index) → TargetHOne i) →+ SourceHOne :=
  FiniteSplitTransfer318.sumPullback pullback

@[expose] def allTransfers : SourceHOne →+ ((i : Index) → TargetHOne i) :=
  FiniteSplitTransfer318.allTransfers transfer

/-- This geometric compatibility has not been established by individual splittings. -/
@[expose] def CrossTermsVanish : Prop :=
  ∀ i j, i ≠ j → ∀ x, transfer i (pullback j x) = 0

/-- No nonzero source-H1 class is invisible to every original normalized transfer. -/
@[expose] def JointlyDetectZero : Prop :=
  ∀ x : SourceHOne, (∀ i, transfer i x = 0) → x = 0

/-- Cross-term vanishing exposes, rather than discards, the common transfer kernel. -/
@[expose] def fivefoldDecomposition (hcross : CrossTermsVanish) :
    SourceHOne ≃+ (((i : Index) → TargetHOne i) × allTransfers.ker) :=
  FiniteSplitTransfer318.decomposition pullback transfer split hcross

theorem fivefoldDecomposition_second (hcross : CrossTermsVanish) (x : SourceHOne) :
    ((fivefoldDecomposition hcross x).2 : SourceHOne) =
      x - ∑ i, pullback i (transfer i x) := rfl

/-- The exact remaining exhaustion condition for the original five pullbacks. -/
theorem sumPullback_surjective_iff (hcross : CrossTermsVanish) :
    Function.Surjective sumPullback ↔ JointlyDetectZero :=
  FiniteSplitTransfer318.surjective_iff_commonKernel_zero pullback transfer split hcross

/-- Conditional endpoint only: both displayed geometric hypotheses remain necessary inputs. -/
@[expose] def fivefoldEquivalence
    (hcross : CrossTermsVanish) (hkernel : JointlyDetectZero) :
    ((i : Index) → TargetHOne i) ≃+ SourceHOne :=
  FiniteSplitTransfer318.equivalence pullback transfer split hcross hkernel

theorem fivefoldEquivalence_apply
    (hcross : CrossTermsVanish) (hkernel : JointlyDetectZero)
    (x : (i : Index) → TargetHOne i) :
    fivefoldEquivalence hcross hkernel x = ∑ i, pullback i (x i) := rfl

theorem fivefoldEquivalence_symm
    (hcross : CrossTermsVanish) (hkernel : JointlyDetectZero) (x : SourceHOne) :
    (fivefoldEquivalence hcross hkernel).symm x = allTransfers x :=
  FiniteSplitTransfer318.equivalence_symm_apply pullback transfer split hcross hkernel x

end ActualFiveHOneDecomposition318
