# Explicit harmonic logarithm in the full five-kernel bound

All1247 predecessor Lean sources remain byte-identical. Four new modules give1251 total. No local Lean/profiling or resource changes; hosted kernel validation remains pending.

The literal complete bin interval[-q,q] is partitioned into its negative tail[-q,-2],central bins{-1,0},and positive tail[1,q]. Both central bins keep their full cost N. The negative tail map b↦-b-1 is injective into[1,q],so no bin or resonance is removed. This proves reciprocalBlockBudget(N,q)<=2N+2q*positiveReciprocalSum(q). Exact reindexing identifies the positive sum with the native harmonic number H(q.toNat). The pinned native harmonic_le_one_add_log theorem then gives the explicit bound2N+2q(1+log q) for positive integer q.

This logarithmic budget is consumed by the COMPLETE even-displacement kernel and then the FULL original smooth five-variable sum, with all five frequency factors already constructed in r13. All support/weight constants precede B,a,q,t. Nonzeroκ and the exact rational approximation hypotheses remain explicit; no gcd(κ,q) condition is added.

Remaining: denominator/error and arc-distribution control on actual minorDomain,possibly refined kernel estimates or moment/integration arguments needed to turn this pointwise bound into integrated o(B³). This packet does not assert that the displayed bound alone is uniformly power-saving on every minor arc. No same-index prime/ray/order/Anchor/rank conclusion.
