# Exact RC62 r7: two diagnosed source owners only

Parent hosted r6 44854060242, 50/62 compiler pass and 766 declarations audited,
2 direct errors, 10 import-blocked, 42 not selected. R7 is source-only until
new validation. All 104 source hashes checked against raw parent inventory;
102 unchanged, including the unselected full-ratio terminal.

* CTActualQuadraticRootSigns318: the public action still uses the exact
  FieldUnitRep K, with two explicitly nested Additive-of-units to units to
  field coercions. The proof body is the exact type-ascribed smul/Units
  pattern from hosted-green CTContinuousFieldHTwo318. Replace parsed
  local-notation V.ρ by declared (FieldUnitRep K).ρ; qualify the actual
  project xor operation, split phase on literal Bool equality before
  converting fieldSign, and use the pinned iff map_ne_zero direction.
  All points, topology, coefficients and true/false sign convention are
  unchanged. No new imports or options.
* CTLiteralDualComposite318: a congruence tactic at the already-earned
  zero-ordinate branch discharged the first explicit bullet on r6.
  A single congr 1 <;> assumption keeps the original two actual coordinate
  equalities and removes the unconditionally opened bullets. No import or
  signature change.

Select only CTActualGloballyFiniteIsogenySelmer318 (same canonical 62 owner
order as parent). The unselected 104-module ratio terminal is included
unchanged as archival material, not claimed passed. There is no parity/rank
or native arithmetic Cassels–Tate conclusion. No local Lean or GitHub write.
