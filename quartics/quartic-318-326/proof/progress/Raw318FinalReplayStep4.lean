module

public import Raw318FinalReplayStep3

public section

namespace Raw318FinalReplay

open CircuitReplay

set_option maxRecDepth 100000

set_option maxHeartbeats 0

set_option linter.unusedSimpArgs false

set_option linter.unusedVariables false

set_option linter.unnecessarySimpa false

set_option linter.unnecessarySeqFocus false



theorem congr4 (S : ℚ) : ∀ q, HasSolution (stage5 S) q ↔ HasSolution (stage4 S) q := by
  apply solutions_congr
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


end Raw318FinalReplay
