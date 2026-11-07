module

public import Raw318FinalReplayData

public section

namespace Raw318FinalReplay

open CircuitReplay

set_option maxRecDepth 100000

set_option maxHeartbeats 0

set_option linter.unusedSimpArgs false

set_option linter.unusedVariables false

set_option linter.unnecessarySimpa false

set_option linter.unnecessarySeqFocus false



theorem congr0 (S : ℚ) : ∀ q, HasSolution (stage1 S) q ↔ HasSolution (stage0 S) q := by
  apply solutions_congr
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


end Raw318FinalReplay
