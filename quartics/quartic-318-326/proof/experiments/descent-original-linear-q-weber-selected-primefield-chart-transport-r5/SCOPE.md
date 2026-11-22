# Selected Gaussian prime-field transport, revision 5

The only changed Lean owner is `ActualGaussianWeberSelectedPrimeFieldFrobTransport318`.
The official revision 4 job 137187531551 selected exactly 20 modules: 19
compiled and 414 declarations passed the axiom audit; the final owner failed.
At lines 55, 58 and 63, bare `FunctionField` resolved to the opened stock
`WeierstrassCurve.Affine.FunctionField` (an affine-curve argument), whereas
the intended source is the already-compiled original-chart
`ActualGaussianWeberGaussLocalization318.FunctionField` (a coefficient
field argument). Qualify that exact identifier in the three diagnosed
positions and both local notations for the same carriers, so later
uses in the proof and its codomain cannot fall back to the conflicting
overload. No imports, statements, proof tactics, or heartbeat settings
are otherwise changed. The official log is retained verbatim.

This receiver transports already-supplied positive coordinates for the
same signed Gaussian generic point to the literal prime-field stock
Frobenius map. It does not supply those positive coordinates, prove
arithmetic Frobenius on original torsion, or prove the downstream norm
statement. This revision has not been tested by Lean. The 9-module chart
subscope is documented but does not contain the repaired owner; the
20-module selector is the smallest existing owner-selected repair gate.

The official ZIP and deterministic delivery archive are retained
off-repository; this packet carries text only.
