# One-Q31 r2: exact tangent negation alias repair

Official One-Q31r1 compiled 29 of 31 with a strict 529-declaration
audit. The fixed-X affine Hensel point and its base maps are accepted.
Only the old PrimaryProbe owner failed; the phase receiver was blocked
and untouched. In the actual doubling proof, instantiate the existing
strict literal negY theorem on exactly (curve K).toAffine at (i,y),
then transit with the already supplied opposite-branch equality.
Nothing else in the proof or its statement changes.

All 30 other owner bytes are exact, including the phase receiver.
The independent repair isolation is PrimaryProbe5; full closure for
the one actual phase theorem is 31/0. The FixedXAffineHenselProbe5
theorem already compiled in the same official run. This source selects
the positive coordinates from supplied four same-point branches;
it does not create those branches, stationarity, or prime occurrence.

Only text in repository packet; physical official artifact off-repository.
No local Lean, dispatch, registry action or push.
