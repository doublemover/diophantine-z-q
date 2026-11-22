# Exact Gauss6 r3: independent-factor rational cross equality

On official r2, PrimitiveRational is strictly green and audited (36
declarations). Only NoDegreeRise then compiled unsuccessfully, because
the two rewrites in its crossed-product identity tried to replace the
indices A,B of the dependent fixed PrimitivePair. Multiply only the
independent polynomial factor using congrArg with a typed K[X] input
on both ends. The middle identity is the same commutative ring identity.
The denominator, numerator, valuation, degree bound and all theorem
statements are unchanged. This is one proof-body hunk in the only
observed red owner, with five other Lean sources byte-identical.

Exact r2 selected orders, official package bytes, raw compiler log,
source hashes and strict PrimitiveRational/36-axiom audit are bound.
The other four downstream sources were blocked, not compiled in r2.
No new native proof acceptance, no local Lean, no broader packet change.
