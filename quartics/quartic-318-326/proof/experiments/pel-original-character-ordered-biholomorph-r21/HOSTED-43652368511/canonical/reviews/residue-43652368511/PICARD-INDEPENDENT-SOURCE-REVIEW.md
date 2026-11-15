# Independent residue carrier-repair source review

Reviewer: Picard sibling agent, distinct from author. Source-level PASS only, not Lean compilation or kernel acceptance.

Read the exact evaluator3 hosted failure log: final7/1 goal still carried ZMod of the unreduced prime vector selector, with unreduced val casts and unused concrete7 coefficient facts. The former simp-only attempt did not make the dependent carrier literal. The new proof keeps symbolic z over its full domain and splits only the four prescribed prime indices. Each branch explicitly changes both z and the entire function Eq carrier to ZMod2/3/5/7 before extensionality. That is a targeted correction of the observed type/instance matching boundary, with no new premise, finite residue enumeration or altered lift.

The four literal whole-function equality targets should make extensionality produce concrete scalar carrier goals; an extra scalar change is not mathematically needed. Hosted elaboration remains required to confirm the type annotations survive the existing normalization/cast chain and match the13 unchanged coefficient facts. No guarantee is asserted that every tactic closure succeeds. Definitions and downstream kernel/range statements are unchanged, and no local Lean was run.

## Exact bindings
- before/PELPrimeLatticeResidues318.lean: 445d1efcc1b027f943fec35c5e56f6098ed0577c99f6c2ed563a5bc19d28bc47
- after/PELPrimeLatticeResidues318.lean: 6becab261123a7a7ca8447b02701107e89868da7a93068ebba330739716bb5d6
- PELPrimeLatticeResidues318.log: 66e311ce076caec42dbc061195268fa0763c9f29911864568c13cddb81a0f7f7
- SOURCE.diff: 01bcb130e75c89a84a7573536dfd2c4a67b3cd6b62a7ca7e82dbe87da05c6a67
