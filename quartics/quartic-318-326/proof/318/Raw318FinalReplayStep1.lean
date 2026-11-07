module

public import Raw318FinalReplayStep0

public section

namespace Raw318FinalReplay

open CircuitReplay

set_option maxRecDepth 100000

set_option maxHeartbeats 0

set_option linter.unusedSimpArgs false

set_option linter.unusedVariables false

set_option linter.unnecessarySimpa false

set_option linter.unnecessarySeqFocus false



theorem congr1 (S : ℚ) : ∀ q, HasSolution (stage2 S) q ↔ HasSolution ((stage1 S).map (fun f => f ∘ (AffineAnchor.forward 55 56 57 S))) q := by
  apply solutions_congr
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


end Raw318FinalReplay
