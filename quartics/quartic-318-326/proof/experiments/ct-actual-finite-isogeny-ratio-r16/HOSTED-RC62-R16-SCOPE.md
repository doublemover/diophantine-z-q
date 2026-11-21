# Exact r15 hosted diagnosis to r16 literal all-place scalar endpoint

Hosted 44873280574 on exact RC62 r15: 61 compile passes, one compiler-error
owner, 42 unselected, 1010 audited. Good local isogeny images passed.
Sole failing source is CTActualGloballyFiniteIsogenySelmer318.
Only three observed sites are repaired:

1. L113: bind the equality (i : Nat) = p explicitly from the obstruction
   p = q i, then rewrite the outside membership target and use i.property.
   This avoids a simplifier pattern on opaque proof-local q.
2. L125: expose the exact scalarSelmer subtype body, with no change to
   the actual all-place conditions, so the public statement can project
   the subtype value. Endpoint structures and proof inputs are unchanged.
3. L176: construct Finite on the literal retained subtype by explicitly
   unfolding retainedCode before instance synthesis. Code n still denotes
   the unchanged product of ZMod 2 and functions on the exact finite prime
   support. Transfer along the existing same equivalence.

The stage verifies all 104 raw ancestor source hashes, all 62 module logs plus the audit log,
one edited owner, 103 unchanged peers, the exact original 62 order,
and unchanged full 104 target source. No local Lean, hosted activation,
or remote writes. The separate scalar-isogeny/CT conclusions remain
outside this Exact RC62 validation scope.
