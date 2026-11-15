module
public import OriginalFiveTransferInvariance318

public section
noncomputable section
namespace OriginalFiveHOneTraceEquivalence318
open ActualFiveHOneDecomposition318 ActualFiveHOneRationalExhaustion318
open ActualSourceHOnePullbacks318 ActualSourceHOneCharacterAction318
open ActualSourceHOneCharacterProjectors318 SourceHOneCharacterIndices318
open scoped BigOperators
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem zero_of_neg_eq_self {M : Type} [AddCommGroup M] [Module ℚ M]
    (x : M) (h : -x = x) : x = 0 := by
  have hs : x+x = 0 := calc
    x+x = (-x)+x := congrArg (fun z => z+x) h.symm
    _ = 0 := neg_add_cancel x
  have hz : (2 : ℚ) • x = 0 := by simpa only [two_smul] using hs
  exact (smul_eq_zero.mp hz).resolve_left (by norm_num)

/-- Actual trace invariance and actual sign characters force every wrong-character trace to vanish. -/
theorem transfer_character_zero (i j : ActualFiveHOneDecomposition318.Index) (hij : i ≠ j) : transfer i (characterClass j) = 0 := by
  apply zero_of_neg_eq_self
  cases i with
  | some k =>
    have h := OriginalFiveTransferInvariance318.character_invariant k (characterClass j)
    rw [action_characterClass,OriginalCharacterPullbackLines318.epsilon_flip,
      if_neg (Ne.symm hij),neg_one_smul,map_neg] at h
    exact h
  | none =>
    cases j with
    | none => exact (hij rfl).elim
    | some k =>
      obtain ⟨b,hb,hk⟩ := OriginalFifthPullbackLine318.even_separates k
      have h := OriginalFiveTransferInvariance318.fifth_invariant b hb (characterClass (some k))
      rw [action_characterClass,hk,neg_one_smul,map_neg] at h
      exact h

/-- Cross-transfer vanishing now concerns the unchanged original five H1 maps. -/
theorem cross_terms : CrossTermsVanish := by
  intro i j hij x
  obtain ⟨q,hq⟩ := OriginalFivePullbackIndependence318.pullback_line j x
  rw [hq]
  change transferLinear i (q • characterClass j) = 0
  rw [map_smul,show transferLinear i (characterClass j) = 0 from transfer_character_zero i j hij,
    smul_zero]

/-- No class of the actual contact H1 survives in the common kernel of the original normalized transfers. -/
theorem common_kernel_zero : JointlyDetectZero :=
  (sumPullback_surjective_iff cross_terms).mp OriginalFiveHOneEquivalence318.original_sum_bijective.2

/-- The prior exact five-pullback equivalence has the original normalized-transfer vector as inverse. -/
theorem original_inverse (y : SourceHOne) :
    OriginalFiveHOneEquivalence318.equivalence.symm y = allTransfers y := by
  have h := FiniteSplitTransfer318.transfer_sum pullback transfer split cross_terms
    (OriginalFiveHOneEquivalence318.equivalence.symm y)
  change allTransfers (OriginalFiveHOneEquivalence318.equivalence
    (OriginalFiveHOneEquivalence318.equivalence.symm y)) = _ at h
  rw [LinearEquiv.apply_symm_apply] at h
  exact h.symm

/-- Fully identified actual rational cohomology decomposition: original pullbacks forward,
original trace/8 transfers backward, with neither geometric input remaining assumed. -/
@[expose] def equivalence : ((i : ActualFiveHOneDecomposition318.Index) → TargetHOne i) ≃ₗ[ℚ] SourceHOne :=
  OriginalFiveHOneEquivalence318.equivalence

theorem equivalence_apply (x : (i : ActualFiveHOneDecomposition318.Index) → TargetHOne i) :
    equivalence x = ∑ i, pullback i (x i) := rfl

theorem equivalence_symm (y : SourceHOne) : equivalence.symm y = fun i => transfer i y :=
  original_inverse y

/-- The original normalized-transfer projections coincide with the genuine geometric character projectors. -/
theorem projection_eq_character (i : ActualFiveHOneDecomposition318.Index) (y : SourceHOne) :
    pullback i (transfer i y) = projector i y := by
  have h := OriginalFiveHOneEquivalence318.inverse_component y i
  rw [original_inverse] at h
  exact h

/-- Whole-H1 identity decomposition through the exact original quotient maps and traces. -/
theorem sum_original_projections (y : SourceHOne) : ∑ i, pullback i (transfer i y) = y := by
  have h := equivalence.apply_symm_apply y
  rw [equivalence_symm,equivalence_apply] at h
  exact h

end OriginalFiveHOneTraceEquivalence318
