# FiniteGeneric28 r2: supply the exact nested helper proof instance

Official r1 compiled all 27 dependencies and audited 500 declarations.
The sole L134 failure is typeclass inference for the automatically
included section variable at the helper call with V replaced by gauss V.
Supply DecidableEq of the nested residue type only in the hspec proof.
The actual reduction ring, its point and coordinates, and its expected
DecidableEq parameters for stock point operations are unchanged.
No statement or import changes. All 27 other proof files are exact,
and the official r1 ZIP, logs and audit are bound.

No r2 acceptance, local Lean run, dispatch, or push.
