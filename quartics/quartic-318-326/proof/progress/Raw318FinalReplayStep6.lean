module

public import Raw318FinalReplayStep5

public section

namespace Raw318FinalReplay

open CircuitReplay

set_option maxRecDepth 100000

set_option maxHeartbeats 0

set_option linter.unusedSimpArgs false

set_option linter.unusedVariables false

set_option linter.unnecessarySimpa false

set_option linter.unnecessarySeqFocus false



theorem source_iff_final (S q : ℚ) : HasSolution (stage0 S) q ↔ HasSolution (stage6 S) q := by
  exact ((congr0 S q).symm).trans (((AffineAnchor.solutions (stage1 S) 55 56 57 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) S q).trans (congr1 S q).symm).trans (((congr2 S q).symm).trans (((AnchorValueShear.solutions (stage3 S) 308 145 (by decide) (by decide) (by decide) S q).trans (congr3 S q).symm).trans (((congr4 S q).symm).trans (((congr5 S q).symm))))))


end Raw318FinalReplay
