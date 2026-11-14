# Scalar pole real-domain lexical normalization (source-only)

Basis: hosted run 43539970197 at 7a5f079f2a82fa6f21db0e060d9bca1af9956a0b, descent predecessor forward-actual-two-descent-root-divisor-orders-r6, artifact 14092022752. ScalarForwardWitness318 passed (5.430 s). The next first failure is ScalarPoleRealDomain318 (4.427 s). Exact own log/RESULT retained.

The log diagnoses both occurrences of `10<inputR` at lines12 and52 as the principal-segment notation `<i` followed by unknown `nputR`: OfNat(Type)10 fails, hr acquires a PrincipalSeg type, three elementary inequalities consequently fail, and packed_bound is not produced for the second theorem. The candidate changes ONLY those two substrings to `10 < inputR`. No proof tactic, coefficient, definition, imported source, resource option or other theorem text changes. This fixes the intended inequality hypothesis tokenization, not a change from a valid inequality to a stronger premise.

## Required and constructed inputs

packed_bound retains arbitrary w:Assignment,n:ℤ and the intended exact rational premise 10<inputR(w0), with 0≤w33≤1, 1/100<|w37|≤1 and |ActualScalarRoot318.inverseNorm n|<1. Its conclusion remains 0<W w n ∧ W w n<10. pole_domain requires precisely the same data and returns 0<poleInput w n ∧ poleInput w n<17. The two repaired premises are both now explicitly the intended ℚ order relation applied to the unchanged ScalarForwardWitness318.inputR.

The source proof still sets r=inputR(w0), bounds the same N and Q, clears the same denominators and consumes the same inverseNorm. All rational constants, powers15/29, strict versus weak inequalities and endpoint exclusions remain unchanged. No selected sample or finite subset replaces the universal w,n domain. No nonzero assumption is added: positivity of r and nonzero w37 are still derived from the same hypotheses.

There are no changed transition/norm/comparison maps: norm, N,Q,W and poleInput definitions are imported unchanged from the verified predecessor ScalarForwardWitness318/ActualScalarRoot318. The returned quantity is exactly the original scalar poleInput, not a substitute positive witness. The actual consumer PreparedIntegerSource318.scalar_domain applies pole_domain to DetectorGateWitness318.witness (a:ℚ) labels h and labels1: integer_inputR_large supplies the repaired rational inequality after witness_input; detector33/common_bounds supply both half-trace bounds; detector37 and hscalar/common_bounds supply the norm bounds; inverseNorm_bound uses hn1 and hn(1). It returns the same scalarB positivity and upper bound. All these consumer source files remain unchanged.

## Scope and verification

Source review must independently check the literal two-token diff against exact diagnostics. Descent's own artifact is established; any weighted propagation must additionally bind that predecessor's own hosted result and source identity. Prior speculative wider spacing and ScalarCompleteSource changes are not included. No local Lean, Lake, kernel acceptance, recursive axiom or full arithmetic theorem check has run; downstream elaboration beyond the malformed-premise errors remains a hosted question. The existing maxHeartbeats0 setting is unchanged, not newly introduced.
