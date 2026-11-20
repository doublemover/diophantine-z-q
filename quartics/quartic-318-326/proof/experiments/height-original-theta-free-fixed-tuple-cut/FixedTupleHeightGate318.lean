module
public import ActualTwoSourceHeightGate318
import all ActualTwoSourceHeightGate318
import all CleanSparseHeightCut318
import all Current318FinalBridge
import all Current318FinalPolynomial
import all Current326Bridge
public section
noncomputable section
namespace FixedTupleHeightGate318
open CircuitReplay Raw318FinalReplay ActualTwoSourceHeightGate318
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-! Preserve the pointwise row proofs already present in the six clean replay
stages. Only their outer solutions_congr (which forgets all coordinates except
0) is omitted. The 1,728 row witnesses below are unchanged. No original file
is changed. In an integrated build these six lemmas could instead be exposed
upstream and used by BOTH their existing existential consumers and this one. -/

private theorem stage_rows0 (S:ℚ) : ∀w, Constraints (stage1 S) w ↔ Constraints (stage0 S) w := by
  apply constraints_congr
  simp only [stage1, stage0, List.map_cons, List.map_nil]
  exact List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (by intro w; have h : r288 S w = (16 : ℚ) * r287 S w := (by unfold r288 r287; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.nil))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

private theorem stage_rows1 (S:ℚ) : ∀w, Constraints (stage2 S) w ↔ Constraints ((stage1 S).map (fun f => f ∘ (AffineAnchor.forward 55 56 57 S))) w := by
  apply constraints_congr
  simp only [stage2, stage1, List.map_cons, List.map_nil]
  exact List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (by intro w; have h : r289 S w = r288 S ((AffineAnchor.forward 55 56 57 S) w) := (by simp only [r289, r288, AffineAnchor.forward] <;> norm_num <;> ring); simpa only [Function.comp_def, h]) (
List.Forall₂.nil))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

private theorem stage_rows2 (S:ℚ) : ∀w, Constraints (stage3 S) w ↔ Constraints (stage2 S) w := by
  apply constraints_congr
  simp only [stage3, stage2, List.map_cons, List.map_nil]
  exact List.Forall₂.cons (by intro w; have h : r290 S w = (-1 : ℚ) * r0 S w := (by unfold r290 r0; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r291 S w = (-1 : ℚ) * r1 S w := (by unfold r291 r1; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r292 S w = (-1 : ℚ) * r2 S w := (by unfold r292 r2; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r293 S w = ((1 / 2) : ℚ) * r3 S w := (by unfold r293 r3; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r294 S w = (-1 : ℚ) * r4 S w := (by unfold r294 r4; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r295 S w = (-1 : ℚ) * r5 S w := (by unfold r295 r5; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r296 S w = (-1 : ℚ) * r6 S w := (by unfold r296 r6; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r297 S w = ((1 / 2) : ℚ) * r7 S w := (by unfold r297 r7; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r298 S w = (-2 : ℚ) * r8 S w := (by unfold r298 r8; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r299 S w = (-1 : ℚ) * r9 S w := (by unfold r299 r9; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r300 S w = (-1 : ℚ) * r10 S w := (by unfold r300 r10; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r301 S w = ((1 / 2) : ℚ) * r11 S w := (by unfold r301 r11; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r302 S w = (-1 : ℚ) * r12 S w := (by unfold r302 r12; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r303 S w = (-1 : ℚ) * r13 S w := (by unfold r303 r13; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r304 S w = (-1 : ℚ) * r14 S w := (by unfold r304 r14; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r305 S w = ((1 / 2) : ℚ) * r15 S w := (by unfold r305 r15; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r306 S w = (-1 : ℚ) * r16 S w := (by unfold r306 r16; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r307 S w = (-1 : ℚ) * r17 S w := (by unfold r307 r17; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r308 S w = (-1 : ℚ) * r18 S w := (by unfold r308 r18; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r309 S w = ((1 / 2) : ℚ) * r19 S w := (by unfold r309 r19; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r310 S w = (-1 : ℚ) * r20 S w := (by unfold r310 r20; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r311 S w = (-1 : ℚ) * r21 S w := (by unfold r311 r21; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r312 S w = (-1 : ℚ) * r22 S w := (by unfold r312 r22; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r313 S w = ((1 / 2) : ℚ) * r23 S w := (by unfold r313 r23; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r314 S w = (-1 : ℚ) * r24 S w := (by unfold r314 r24; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r315 S w = (-1 : ℚ) * r25 S w := (by unfold r315 r25; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r316 S w = (-1 : ℚ) * r26 S w := (by unfold r316 r26; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r317 S w = ((1 / 2) : ℚ) * r27 S w := (by unfold r317 r27; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r318 S w = (-1 : ℚ) * r28 S w := (by unfold r318 r28; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r319 S w = (-1 : ℚ) * r29 S w := (by unfold r319 r29; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r320 S w = (-1 : ℚ) * r30 S w := (by unfold r320 r30; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r321 S w = ((1 / 2) : ℚ) * r31 S w := (by unfold r321 r31; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r322 S w = (-1 : ℚ) * r32 S w := (by unfold r322 r32; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r323 S w = (-1 : ℚ) * r33 S w := (by unfold r323 r33; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r324 S w = (-1 : ℚ) * r34 S w := (by unfold r324 r34; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r325 S w = (-1 : ℚ) * r35 S w := (by unfold r325 r35; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r326 S w = (8 : ℚ) * r36 S w := (by unfold r326 r36; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r327 S w = (8 : ℚ) * r37 S w := (by unfold r327 r37; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r328 S w = (-1 : ℚ) * r38 S w := (by unfold r328 r38; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r329 S w = (-1 : ℚ) * r39 S w := (by unfold r329 r39; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r330 S w = (-1 : ℚ) * r40 S w := (by unfold r330 r40; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r331 S w = (-1 : ℚ) * r41 S w := (by unfold r331 r41; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r332 S w = (-1 : ℚ) * r42 S w := (by unfold r332 r42; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r333 S w = (-1 : ℚ) * r43 S w := (by unfold r333 r43; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r334 S w = (-1 : ℚ) * r44 S w := (by unfold r334 r44; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r335 S w = (-1 : ℚ) * r45 S w := (by unfold r335 r45; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r336 S w = (-1 : ℚ) * r46 S w := (by unfold r336 r46; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r337 S w = (-1 : ℚ) * r47 S w := (by unfold r337 r47; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r338 S w = (-1 : ℚ) * r48 S w := (by unfold r338 r48; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r339 S w = (-1 : ℚ) * r49 S w := (by unfold r339 r49; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r340 S w = (-1 : ℚ) * r50 S w := (by unfold r340 r50; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r341 S w = (-1 : ℚ) * r51 S w := (by unfold r341 r51; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r342 S w = (-1 : ℚ) * r52 S w := (by unfold r342 r52; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r343 S w = (-195 : ℚ) * r53 S w := (by unfold r343 r53; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r344 S w = (-195 : ℚ) * r54 S w := (by unfold r344 r54; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r345 S w = (8 : ℚ) * r55 S w := (by unfold r345 r55; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r346 S w = (-8 : ℚ) * r56 S w := (by unfold r346 r56; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r347 S w = (-195 : ℚ) * r57 S w := (by unfold r347 r57; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r348 S w = (195 : ℚ) * r58 S w := (by unfold r348 r58; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r349 S w = (-195 : ℚ) * r59 S w := (by unfold r349 r59; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r350 S w = (195 : ℚ) * r60 S w := (by unfold r350 r60; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r351 S w = (-195 : ℚ) * r61 S w := (by unfold r351 r61; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r352 S w = (195 : ℚ) * r62 S w := (by unfold r352 r62; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r353 S w = (-8 : ℚ) * r63 S w := (by unfold r353 r63; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r354 S w = (8 : ℚ) * r64 S w := (by unfold r354 r64; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r355 S w = (5 : ℚ) * r65 S w := (by unfold r355 r65; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r356 S w = (-5 : ℚ) * r66 S w := (by unfold r356 r66; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r357 S w = (-8 : ℚ) * r67 S w := (by unfold r357 r67; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r358 S w = (8 : ℚ) * r68 S w := (by unfold r358 r68; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (by intro w; have h : r359 S w = (-8 : ℚ) * r71 S w := (by unfold r359 r71; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r360 S w = (8 : ℚ) * r72 S w := (by unfold r360 r72; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (by intro w; have h : r361 S w = (-8 : ℚ) * r75 S w := (by unfold r361 r75; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r362 S w = (8 : ℚ) * r76 S w := (by unfold r362 r76; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (by intro w; have h : r363 S w = (-1 : ℚ) * r79 S w := (by unfold r363 r79; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r364 S w = (-1 : ℚ) * r80 S w := (by unfold r364 r80; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r365 S w = (-1 : ℚ) * r81 S w := (by unfold r365 r81; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r366 S w = (-1 : ℚ) * r82 S w := (by unfold r366 r82; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r367 S w = (-1 : ℚ) * r83 S w := (by unfold r367 r83; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r368 S w = (-1 : ℚ) * r84 S w := (by unfold r368 r84; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r369 S w = (-2 : ℚ) * r85 S w := (by unfold r369 r85; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r370 S w = (-1 : ℚ) * r86 S w := (by unfold r370 r86; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r371 S w = (-1 : ℚ) * r87 S w := (by unfold r371 r87; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r372 S w = (-1 : ℚ) * r88 S w := (by unfold r372 r88; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r373 S w = (-1 : ℚ) * r89 S w := (by unfold r373 r89; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r374 S w = (-1 : ℚ) * r90 S w := (by unfold r374 r90; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r375 S w = (-1 : ℚ) * r91 S w := (by unfold r375 r91; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r376 S w = (-1 : ℚ) * r92 S w := (by unfold r376 r92; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r377 S w = (-1 : ℚ) * r93 S w := (by unfold r377 r93; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r378 S w = (-1 : ℚ) * r94 S w := (by unfold r378 r94; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r379 S w = (-1 : ℚ) * r95 S w := (by unfold r379 r95; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r380 S w = (-221771664 : ℚ) * r96 S w := (by unfold r380 r96; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r381 S w = (-14892 : ℚ) * r97 S w := (by unfold r381 r97; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r382 S w = (-1 : ℚ) * r98 S w := (by unfold r382 r98; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r383 S w = (-1 : ℚ) * r99 S w := (by unfold r383 r99; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r384 S w = (-1 : ℚ) * r100 S w := (by unfold r384 r100; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r385 S w = (-1 : ℚ) * r101 S w := (by unfold r385 r101; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r386 S w = (-1 : ℚ) * r102 S w := (by unfold r386 r102; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r387 S w = (-1 : ℚ) * r103 S w := (by unfold r387 r103; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r388 S w = (-1 : ℚ) * r104 S w := (by unfold r388 r104; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r389 S w = (-1 : ℚ) * r105 S w := (by unfold r389 r105; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r390 S w = (-1 : ℚ) * r106 S w := (by unfold r390 r106; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r391 S w = (-1 : ℚ) * r107 S w := (by unfold r391 r107; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r392 S w = (-1 : ℚ) * r108 S w := (by unfold r392 r108; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r393 S w = (-1 : ℚ) * r109 S w := (by unfold r393 r109; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r394 S w = (-3081901 : ℚ) * r110 S w := (by unfold r394 r110; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (by intro w; have h : r395 S w = (-1952786 : ℚ) * r112 S w := (by unfold r395 r112; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (by intro w; have h : r396 S w = (-1 : ℚ) * r114 S w := (by unfold r396 r114; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r397 S w = (-1 : ℚ) * r115 S w := (by unfold r397 r115; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (by intro w; have h : r398 S w = (-1 : ℚ) * r120 S w := (by unfold r398 r120; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r399 S w = (-1 : ℚ) * r121 S w := (by unfold r399 r121; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r400 S w = (-1 : ℚ) * r122 S w := (by unfold r400 r122; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r401 S w = (-1 : ℚ) * r123 S w := (by unfold r401 r123; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r402 S w = (-1 : ℚ) * r124 S w := (by unfold r402 r124; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r403 S w = (-1 : ℚ) * r125 S w := (by unfold r403 r125; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r404 S w = (-1 : ℚ) * r126 S w := (by unfold r404 r126; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r405 S w = (-1 : ℚ) * r127 S w := (by unfold r405 r127; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r406 S w = (-1 : ℚ) * r128 S w := (by unfold r406 r128; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r407 S w = (-1 : ℚ) * r129 S w := (by unfold r407 r129; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r408 S w = (-1 : ℚ) * r130 S w := (by unfold r408 r130; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (by intro w; have h : r409 S w = (-1 : ℚ) * r132 S w := (by unfold r409 r132; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (by intro w; have h : r410 S w = (-1 : ℚ) * r134 S w := (by unfold r410 r134; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (by intro w; have h : r411 S w = (-1 : ℚ) * r136 S w := (by unfold r411 r136; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (by intro w; have h : r412 S w = (-1 : ℚ) * r138 S w := (by unfold r412 r138; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r413 S w = (-1 : ℚ) * r139 S w := (by unfold r413 r139; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r414 S w = (-1 : ℚ) * r140 S w := (by unfold r414 r140; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r415 S w = (-1 : ℚ) * r141 S w := (by unfold r415 r141; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r416 S w = (-1 : ℚ) * r142 S w := (by unfold r416 r142; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r417 S w = (-1 : ℚ) * r143 S w := (by unfold r417 r143; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r418 S w = (-1 : ℚ) * r144 S w := (by unfold r418 r144; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r419 S w = (-1 : ℚ) * r145 S w := (by unfold r419 r145; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r420 S w = (-1 : ℚ) * r146 S w := (by unfold r420 r146; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (by intro w; have h : r421 S w = (-2 : ℚ) * r150 S w := (by unfold r421 r150; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (by intro w; have h : r422 S w = (-1 : ℚ) * r152 S w := (by unfold r422 r152; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r423 S w = (-1 : ℚ) * r153 S w := (by unfold r423 r153; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (by intro w; have h : r424 S w = (-3 : ℚ) * r155 S w := (by unfold r424 r155; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (by intro w; have h : r425 S w = (-1 : ℚ) * r157 S w := (by unfold r425 r157; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r426 S w = (-1 : ℚ) * r158 S w := (by unfold r426 r158; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r427 S w = (-1 : ℚ) * r159 S w := (by unfold r427 r159; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r428 S w = (-1205412 : ℚ) * r160 S w := (by unfold r428 r160; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r429 S w = (-1 : ℚ) * r161 S w := (by unfold r429 r161; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r430 S w = (-1 : ℚ) * r162 S w := (by unfold r430 r162; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r431 S w = (-1 : ℚ) * r163 S w := (by unfold r431 r163; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r432 S w = (-1952786 : ℚ) * r164 S w := (by unfold r432 r164; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r433 S w = (-2 : ℚ) * r165 S w := (by unfold r433 r165; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (by intro w; have h : r434 S w = (-1 : ℚ) * r167 S w := (by unfold r434 r167; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r435 S w = (-1 : ℚ) * r168 S w := (by unfold r435 r168; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (by intro w; have h : r436 S w = (-1 : ℚ) * r170 S w := (by unfold r436 r170; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (by intro w; have h : r437 S w = (-1 : ℚ) * r173 S w := (by unfold r437 r173; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r438 S w = (-1 : ℚ) * r174 S w := (by unfold r438 r174; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r439 S w = (-1 : ℚ) * r175 S w := (by unfold r439 r175; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r440 S w = (-1 : ℚ) * r176 S w := (by unfold r440 r176; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r441 S w = (-1 : ℚ) * r177 S w := (by unfold r441 r177; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r442 S w = (-1 : ℚ) * r178 S w := (by unfold r442 r178; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r443 S w = (-1 : ℚ) * r179 S w := (by unfold r443 r179; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r444 S w = (-1 : ℚ) * r180 S w := (by unfold r444 r180; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r445 S w = (-1 : ℚ) * r181 S w := (by unfold r445 r181; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r446 S w = (-1 : ℚ) * r182 S w := (by unfold r446 r182; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r447 S w = (-1 : ℚ) * r183 S w := (by unfold r447 r183; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (by intro w; have h : r448 S w = (-1 : ℚ) * r185 S w := (by unfold r448 r185; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (by intro w; have h : r449 S w = (-1 : ℚ) * r187 S w := (by unfold r449 r187; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (by intro w; have h : r450 S w = (-1 : ℚ) * r189 S w := (by unfold r450 r189; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (by intro w; have h : r451 S w = (-1 : ℚ) * r191 S w := (by unfold r451 r191; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r452 S w = (-1 : ℚ) * r192 S w := (by unfold r452 r192; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r453 S w = (-1 : ℚ) * r193 S w := (by unfold r453 r193; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r454 S w = (-1 : ℚ) * r194 S w := (by unfold r454 r194; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r455 S w = (-1 : ℚ) * r195 S w := (by unfold r455 r195; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r456 S w = (-1 : ℚ) * r196 S w := (by unfold r456 r196; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r457 S w = (-1 : ℚ) * r197 S w := (by unfold r457 r197; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r458 S w = (-1 : ℚ) * r198 S w := (by unfold r458 r198; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r459 S w = (-1 : ℚ) * r199 S w := (by unfold r459 r199; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (by intro w; have h : r460 S w = (-2 : ℚ) * r203 S w := (by unfold r460 r203; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r461 S w = (-1 : ℚ) * r204 S w := (by unfold r461 r204; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r462 S w = (-1 : ℚ) * r205 S w := (by unfold r462 r205; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r463 S w = (-1 : ℚ) * r206 S w := (by unfold r463 r206; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (by intro w; have h : r464 S w = (-3 : ℚ) * r208 S w := (by unfold r464 r208; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (by intro w; have h : r465 S w = (-1 : ℚ) * r210 S w := (by unfold r465 r210; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r466 S w = (-1 : ℚ) * r211 S w := (by unfold r466 r211; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r467 S w = (-1 : ℚ) * r212 S w := (by unfold r467 r212; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r468 S w = (-1205412 : ℚ) * r213 S w := (by unfold r468 r213; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r469 S w = (-1 : ℚ) * r214 S w := (by unfold r469 r214; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r470 S w = (-1 : ℚ) * r215 S w := (by unfold r470 r215; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r471 S w = (-1 : ℚ) * r216 S w := (by unfold r471 r216; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r472 S w = (-1952786 : ℚ) * r217 S w := (by unfold r472 r217; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r473 S w = (-2 : ℚ) * r218 S w := (by unfold r473 r218; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (by intro w; have h : r474 S w = (-1 : ℚ) * r220 S w := (by unfold r474 r220; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r475 S w = (-1 : ℚ) * r221 S w := (by unfold r475 r221; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (by intro w; have h : r476 S w = (-1 : ℚ) * r223 S w := (by unfold r476 r223; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (by intro w; have h : r477 S w = (-1 : ℚ) * r226 S w := (by unfold r477 r226; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r478 S w = (-1 : ℚ) * r227 S w := (by unfold r478 r227; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r479 S w = (-1 : ℚ) * r228 S w := (by unfold r479 r228; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r480 S w = (-1 : ℚ) * r229 S w := (by unfold r480 r229; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r481 S w = (-1 : ℚ) * r230 S w := (by unfold r481 r230; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r482 S w = (-1 : ℚ) * r231 S w := (by unfold r482 r231; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r483 S w = (-1 : ℚ) * r232 S w := (by unfold r483 r232; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r484 S w = (-1 : ℚ) * r233 S w := (by unfold r484 r233; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r485 S w = (-1 : ℚ) * r234 S w := (by unfold r485 r234; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r486 S w = (-1 : ℚ) * r235 S w := (by unfold r486 r235; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r487 S w = (-1 : ℚ) * r236 S w := (by unfold r487 r236; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (by intro w; have h : r488 S w = (-1 : ℚ) * r238 S w := (by unfold r488 r238; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (by intro w; have h : r489 S w = (-1 : ℚ) * r240 S w := (by unfold r489 r240; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (by intro w; have h : r490 S w = (-1 : ℚ) * r242 S w := (by unfold r490 r242; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (by intro w; have h : r491 S w = (-1 : ℚ) * r244 S w := (by unfold r491 r244; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r492 S w = (-1 : ℚ) * r245 S w := (by unfold r492 r245; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r493 S w = (-1 : ℚ) * r246 S w := (by unfold r493 r246; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r494 S w = (-1 : ℚ) * r247 S w := (by unfold r494 r247; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r495 S w = (-1 : ℚ) * r248 S w := (by unfold r495 r248; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r496 S w = (-1 : ℚ) * r249 S w := (by unfold r496 r249; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r497 S w = (-1 : ℚ) * r250 S w := (by unfold r497 r250; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r498 S w = (-1 : ℚ) * r251 S w := (by unfold r498 r251; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r499 S w = (-1 : ℚ) * r252 S w := (by unfold r499 r252; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (by intro w; have h : r500 S w = (-2 : ℚ) * r256 S w := (by unfold r500 r256; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r501 S w = (-1 : ℚ) * r257 S w := (by unfold r501 r257; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r502 S w = (-1 : ℚ) * r258 S w := (by unfold r502 r258; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r503 S w = (-1 : ℚ) * r259 S w := (by unfold r503 r259; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (by intro w; have h : r504 S w = (-3 : ℚ) * r261 S w := (by unfold r504 r261; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (by intro w; have h : r505 S w = (-1 : ℚ) * r263 S w := (by unfold r505 r263; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r506 S w = (-100291113 : ℚ) * r264 S w := (by unfold r506 r264; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r507 S w = (-1 : ℚ) * r265 S w := (by unfold r507 r265; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r508 S w = (-1 : ℚ) * r266 S w := (by unfold r508 r266; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r509 S w = (-1 : ℚ) * r267 S w := (by unfold r509 r267; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r510 S w = (-1 : ℚ) * r268 S w := (by unfold r510 r268; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r511 S w = (-1 : ℚ) * r269 S w := (by unfold r511 r269; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r512 S w = (-1 : ℚ) * r270 S w := (by unfold r512 r270; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r513 S w = (-1 : ℚ) * r271 S w := (by unfold r513 r271; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r514 S w = (-8 : ℚ) * r272 S w := (by unfold r514 r272; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r515 S w = (4 : ℚ) * r273 S w := (by unfold r515 r273; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r516 S w = (-1 : ℚ) * r274 S w := (by unfold r516 r274; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r517 S w = (-1 : ℚ) * r275 S w := (by unfold r517 r275; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (by intro w; have h : r518 S w = (-1 : ℚ) * r277 S w := (by unfold r518 r277; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r519 S w = (-1 : ℚ) * r278 S w := (by unfold r519 r278; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r520 S w = (-1 : ℚ) * r279 S w := (by unfold r520 r279; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r521 S w = (-1 : ℚ) * r280 S w := (by unfold r521 r280; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (by intro w; have h : r522 S w = (-1 : ℚ) * r282 S w := (by unfold r522 r282; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r523 S w = (-1 : ℚ) * r283 S w := (by unfold r523 r283; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r524 S w = (-3 : ℚ) * r284 S w := (by unfold r524 r284; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.nil))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

private theorem stage_rows3 (S:ℚ) : ∀w, Constraints (stage4 S) w ↔ Constraints ((stage3 S).map (fun f => f ∘ (AnchorValueShear.forward 308 145 S))) w := by
  apply constraints_congr
  simp only [stage4, stage3, List.map_cons, List.map_nil]
  exact List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (by intro w; have h : r525 S w = r390 S ((AnchorValueShear.forward 308 145 S) w) := (by simp only [r525, r390, AnchorValueShear.forward] <;> norm_num <;> ring); simpa only [Function.comp_def, h]) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (by intro w; have h : r526 S w = r425 S ((AnchorValueShear.forward 308 145 S) w) := (by simp only [r526, r425, AnchorValueShear.forward] <;> norm_num <;> ring); simpa only [Function.comp_def, h]) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (by intro w; have h : r527 S w = r465 S ((AnchorValueShear.forward 308 145 S) w) := (by simp only [r527, r465, AnchorValueShear.forward] <;> norm_num <;> ring); simpa only [Function.comp_def, h]) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (by intro w; have h : r528 S w = r517 S ((AnchorValueShear.forward 308 145 S) w) := (by simp only [r528, r517, AnchorValueShear.forward] <;> norm_num <;> ring); simpa only [Function.comp_def, h]) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (by intro w; have h : r529 S w = r518 S ((AnchorValueShear.forward 308 145 S) w) := (by simp only [r529, r518, AnchorValueShear.forward] <;> norm_num <;> ring); simpa only [Function.comp_def, h]) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (by intro w; have h : r530 S w = r289 S ((AnchorValueShear.forward 308 145 S) w) := (by simp only [r530, r289, AnchorValueShear.forward] <;> norm_num <;> ring); simpa only [Function.comp_def, h]) (
List.Forall₂.nil))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

private theorem stage_rows4 (S:ℚ) : ∀w, Constraints (stage5 S) w ↔ Constraints (stage4 S) w := by
  apply constraints_congr
  simp only [stage5, stage4, List.map_cons, List.map_nil]
  exact List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (by intro w; have h : r531 S w = (4096 : ℚ) * r525 S w := (by unfold r531 r525; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (by intro w; have h : r532 S w = (16777216 : ℚ) * r526 S w := (by unfold r532 r526; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (by intro w; have h : r533 S w = (16777216 : ℚ) * r527 S w := (by unfold r533 r527; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (by intro w; have h : r534 S w = (-1 : ℚ) * r529 S w := (by unfold r534 r529; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.nil))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

private theorem stage_rows5 (S:ℚ) : ∀w, Constraints (stage6 S) w ↔ Constraints (stage5 S) w := by
  apply constraints_congr
  simp only [stage6, stage5, List.map_cons, List.map_nil]
  exact List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.nil))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


def padded (v:Fin 318→ℚ) : Assignment := fun i=>if h:i<318 then v ⟨i,h⟩ else 0
def lift (v:Fin 318→ℚ) : Assignment :=
  AffineAnchor.forward 55 56 57 scale (AnchorValueShear.forward 308 145 scale (padded v))

private theorem indexed (v:Fin 318→ℚ) : (fun j=>padded v (Current318FinalBridge.index j))=v := by
  ext j
  simp [padded,Current318FinalBridge.index,gapOffset,j.isLt]

theorem rows_lift (v:Fin 318→ℚ)
    (h:SparseQuartic.Constraints Current318FinalPolynomial.scale Current318FinalPolynomial.rows v) :
    Source (lift v) := by
  let a:=padded v
  let b:=AnchorValueShear.forward 308 145 scale a
  let c:=AffineAnchor.forward 55 56 57 scale b
  have hS : (Current318FinalPolynomial.scale:ℚ)=scale := by
    simp only [Current318FinalPolynomial.scale,Int.cast_pow,Int.cast_ofNat] <;> rfl
  have h6' : Constraints (stage6 (Current318FinalPolynomial.scale:ℚ)) a := by
    apply (Current318FinalBridge.interpreted_constraints _ a).mpr
    change SparseQuartic.Constraints Current318FinalPolynomial.scale Current318FinalPolynomial.rows
      (fun j=>padded v (Current318FinalBridge.index j))
    rw [indexed]
    exact h
  have h6 : Constraints (stage6 scale) a := hS ▸ h6'
  have h5 := (stage_rows5 scale a).mp h6
  have h4 := (stage_rows4 scale a).mp h5
  have h3 : Constraints (stage3 scale) b :=
    (constraints_map _ _ _).mp ((stage_rows3 scale a).mp h4)
  have h2 := (stage_rows2 scale b).mp h3
  have h1 : Constraints (stage1 scale) c :=
    (constraints_map _ _ _).mp ((stage_rows1 scale b).mp h2)
  exact (stage_rows0 scale c).mp h1

/-- No existential transport: the displayed three raw witnesses come from
this v itself. Four input coordinates are untouched by all nontrivial shears. -/
theorem slots (v:Fin 318→ℚ) : lift v 0=v 0 ∧
    RawWeights318.t0 scale (lift v)=v 38 ∧ RawWeights318.t1 scale (lift v)=v 194 ∧
    RawWeights318.t2 scale (lift v)=v 245 := by
  norm_num [lift,padded,AffineAnchor.forward,AnchorValueShear.forward,
    RawWeights318.t0,RawWeights318.t1,RawWeights318.t2]

def det (q0 q1 q2:ℚ) : ℚ := bigger (bigger q0 q1) q2
def first (q0 q1 q2 q:ℚ) : Option (ℤ×ℤ) := by
  classical
  let z:=det q0 q1 q2
  let b:=3723*(2*q+1)^2
  exact if CleanSparseHeightCut318.Extreme (detU z) z.num then some (detU z,z.num)
    else if b≠0 ∧ CleanSparseHeightCut318.Extreme b.num b.den then some (b.num,(b.den:ℤ)) else none

theorem selected_slots (v:Fin 318→ℚ) :
    firstExtreme (lift v)=first (v 38) (v 194) (v 245) (v 0) := by
  classical
  obtain ⟨h0,h1,h2,h3⟩:=slots v
  have hd : winner (lift v)=det (v 38) (v 194) (v 245) := by
    simp only [winner,det,h1,h2,h3]
  have hb : beta (lift v)=3723*(2*v 0+1)^2 := by simp only [beta,ScalarSource318.beta,h0]
  simp only [firstExtreme,first,detPair,scalarPair,hd,hb]

def SharpAt (p:ℤ×ℤ) : Prop :=
  ContactHeight318.pointHeight p.1 p.2<27506231*((CleanSparseHeightCut318.S p.1 p.2:ℝ)^2*
    Real.log (CleanSparseHeightCut318.S p.1 p.2:ℝ))

theorem fixed318 (v:Fin 318→ℚ)
    (h:MvPolynomial.eval₂Hom (Int.castRingHom ℚ) v Current318FinalPolynomial.P=0)
    (geom:∀p,first (v 38) (v 194) (v 245) (v 0)=some p → SharpAt p) :
    ∃z:ℤ,(z:ℚ)=v 0 := by
  have hs:=rows_lift v ((Current318FinalPolynomial.zero_iff_constraints v).mp h)
  have hgeom : OneSharp (lift v) := by
    intro p hp
    exact geom p (by simpa only [selected_slots] using hp)
  obtain ⟨z,hz⟩:=source_of_one_sharp (lift v) hs hgeom
  exact ⟨z,hz.trans (slots v).1⟩

theorem fixed326 (v:Fin 326→ℚ)
    (h:MvPolynomial.eval₂Hom (Int.castRingHom ℚ) v Current326CoefficientBinding.tablePolynomial=0)
    (geom:∀p,first (v 38) (v 194) (v 245) (v 0)=some p → SharpAt p) :
    ∃z:ℤ,(z:ℚ)=v 0 := by
  rw [Current326CoefficientBinding.table_eq_sos] at h
  have hs:=((Current326Bridge.constraints_iff v).mp ((Current326Polynomial.zero_iff_constraints v).mp h)).1
  exact fixed318 (Current326Bridge.restrict v)
    ((Current318FinalPolynomial.zero_iff_constraints _).mpr hs) geom

def CounterAt (p:ℤ×ℤ) : Prop :=
  CleanSparseHeightCut318.Extreme p.1 p.2 ∧ IsCoprime p.1 p.2 ∧
  (∀j:Fin 5,ContactRadical318.forms p.1 p.2 j≠0) ∧ ¬SharpAt p

private theorem counter_rows (v:Fin 318→ℚ)
    (h:SparseQuartic.Constraints Current318FinalPolynomial.scale Current318FinalPolynomial.rows v)
    (nonint:¬∃z:ℤ,(z:ℚ)=v 0) :
    ∃p:ℤ×ℤ,first (v 38) (v 194) (v 245) (v 0)=some p ∧ CounterAt p := by
  have hn : ¬∃z:ℤ,(z:ℚ)=lift v 0 := by
    rintro ⟨z,hz⟩;exact nonint ⟨z,hz.trans (slots v).1⟩
  obtain ⟨p,hp,he,hc,hf,hbad⟩:=selected_obstruction (lift v) (rows_lift v h) hn
  exact ⟨p,by simpa only [selected_slots] using hp,he,hc,hf,not_lt_of_ge hbad⟩

theorem counter318 (q:ℚ) (tail:Fin 317→ℚ)
    (h:MvPolynomial.eval₂Hom (Int.castRingHom ℚ) (Fin.cons q tail) Current318FinalPolynomial.P=0)
    (ni:¬∃z:ℤ,(z:ℚ)=q) : ∃p:ℤ×ℤ,first (tail 37) (tail 193) (tail 244) q=some p ∧ CounterAt p :=
  counter_rows (Fin.cons q tail) ((Current318FinalPolynomial.zero_iff_constraints _).mp h) ni

theorem counter326 (q:ℚ) (tail:Fin 325→ℚ)
    (h:MvPolynomial.eval₂Hom (Int.castRingHom ℚ) (Fin.cons q tail)
      Current326CoefficientBinding.tablePolynomial=0) (ni:¬∃z:ℤ,(z:ℚ)=q) :
    ∃p:ℤ×ℤ,first (tail 37) (tail 193) (tail 244) q=some p ∧ CounterAt p := by
  rw [Current326CoefficientBinding.table_eq_sos] at h
  have hs:=((Current326Bridge.constraints_iff (Fin.cons q tail)).mp
    ((Current326Polynomial.zero_iff_constraints _).mp h)).1
  exact counter_rows (Current326Bridge.restrict (Fin.cons q tail)) hs ni

/-- Literal witness-tail indices 37,193,244 (not 38,194,245): q is the head.
The hypotheses and conclusion apply to the SPECIFIED polynomial witness. -/
theorem tail318 (q:ℚ) (tail:Fin 317→ℚ)
    (h:MvPolynomial.eval₂Hom (Int.castRingHom ℚ) (Fin.cons q tail) Current318FinalPolynomial.P=0)
    (geom:∀p,first (tail 37) (tail 193) (tail 244) q=some p → SharpAt p) :
    ∃z:ℤ,(z:ℚ)=q := fixed318 (Fin.cons q tail) h geom

theorem tail326 (q:ℚ) (tail:Fin 325→ℚ)
    (h:MvPolynomial.eval₂Hom (Int.castRingHom ℚ) (Fin.cons q tail)
      Current326CoefficientBinding.tablePolynomial=0)
    (geom:∀p,first (tail 37) (tail 193) (tail 244) q=some p → SharpAt p) :
    ∃z:ℤ,(z:ℚ)=q := fixed326 (Fin.cons q tail) h geom

end FixedTupleHeightGate318
#print axioms FixedTupleHeightGate318.rows_lift
#print axioms FixedTupleHeightGate318.selected_slots
#print axioms FixedTupleHeightGate318.counter318
#print axioms FixedTupleHeightGate318.counter326
#print axioms FixedTupleHeightGate318.tail318
#print axioms FixedTupleHeightGate318.tail326
