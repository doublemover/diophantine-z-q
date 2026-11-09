# Actual translated scalar index and two/three preparation

Status: source draft, pending hosted Lean validation and distinct bounded review. No local Lean compilation or build was run. This does not prove the full 318/326 arithmetic theorem.

## Retained source and exact branch

The historical V10 source at `docs/sources/quartic_v10.tex`, subsection `subsec:v9-completeness`, chooses an arbitrarily divisible positive scalar index s before real neighborhoods and contact primes, then uses the label a=s+1. The current `docs/arithmetic.md` section `square-root-kummer-scalar` explicitly retains the minus branch for completeness. These are prior inputs, not a new proof of their entire local preparation. The actual 318 source has denominator exponent15 and valuation coefficient29; the older source's numerical stages cannot be substituted silently.

`ScalarTranslatedIndex318` applies the original coherent group law to nR and −R. The actual generator has u(1)=1/k and v(1)=m/k². Consequently

u(n−1) = −u(n) * shiftWitness(u(n),v(n)).

The literal scalar root −1/(u*shift) is therefore +1/u(n−1), not the negative fixedRoot(n−1). Its inverse norm is exactly normCoefficient(u(n−1)); no independent Kummer sign or related point is substituted.

## Exact local depths on actual leaves

`ScalarIndexValuations318` applies the retained original-point multiple theorems, not a new arbitrary valuation model. For nonzero n, v₂(norm u(n))=3+2v₂(n). For nonzero even n, v₃(norm u(n))=2+2v₃(n). The scalar inverse norm has these values at n−1.

`ScalarHalfTraceDepth318` uses the actual half-trace f=(u²).re=a²+2b². At2 the two term valuations have opposite parity, so v₂(f)=v₂(norm u). At3 the inert norm has valuation twice the minimum coefficient valuation, so v₃(f)≥v₃(norm u). Both proofs retain zero coefficient branches and use actual nonzero norm to exclude f=0.

The current integer scalar polynomial r has valuations2,0,0 at2,3,17. This is obtained from the exact multiplier114444*r values4,2,2 and114444=2²*28611=3²*12716=17²*396. `ScalarTwoThreePreparation318` now proves the actual W unit conditions under integer-index depth conditions:

- At2, v₂(n−1)≥v₂(h)+15. The15 is exact: 2(3+2(x+15))−[2(3+2x)+29*2]=2>0.
- At3, both h and n−1 are even and v₃(n−1)>v₃(h).

These theorems retain general h and label depths; they do not require the later illustrative congruence.

## Concrete fixed labels and preservation by the same CRT

Choose any positive natural d before the real region, threshold and contact-prime data. Set the second fixed label to1+6^21*d. It is odd, is1 modulo3, exceeds1, and its translated index has both2/3 depths at least21. The free multiplier d retains flexibility for further arithmetic conditions; those conditions are not claimed solved here.

If h≡64 modulo384, then v₂(h)=6 and v₃(h)=0. These give both actual W units. The original continuity congruence h≡h₀ moduloL preserves them whenever384 dividesL and h₀≡64 modulo384. These restrictions are additional explicit inputs, not silently obtained from all previous moduli. In particular this concrete residue is not a claim to realize other detector local conditions; the more general depth theorems remain available when those conditions require another residue.

`PreparedTwoThreeSource318.current_source_prepared_two_three` consumes the same chosen h from the existing real/CRT family. It preserves the original input a, all fixed roots, scalar real bound, contact parameter t, pole inputs at190/241/292 and the scalar pole. Its conclusion now supplies both2/3 W units without local-depth premises there. At all other positive-support primes the actual leaf-depth conditions remain explicit. Together they give the actual square reduced scalar denominator and exact4/2/2 values. Four actual two-twist realizations and the explicit final ternary Anchor still supply the literal current-scale full288-row HasSolution.

## Open joins and verification scope

Still open: preparation at other scalar support primes (including17), local preparation for the three detector poles, compatible prime/ray pattern and fixed-label/Lucas choices, actual simultaneous two-twist rational-point production, and the final Anchor producer. The actual local squares at2,3,17 from the predecessor are unchanged. No local square-to-rational-point implication is inferred.

This97-source packet contains91 byte-identical sources from `forward-two-twist-realization-r2` and six new sources. The predecessor's narrow parser/instance-visibility diagnostic repair is retained unchanged and remains subject to hosted validation. New modules have finite1,000,000 heartbeat limits. The symbolic checker verifies displayed rational identities and constant/depth arithmetic; finite congruence samples are sanity checks only. The source-policy/dependency closure and audit selftests are structural checks, not kernel or whole-proof acceptance.

## Normalization proof-boundary repair and diagnostics

Hosted204e9b7 still reaches deterministic whnf/isDefEq limits at the concrete normalized-point curve-proof arguments, although the abstract normalized_curve theorem passes and the earlier parser error is gone. This successor leaves96sources byte-identical. In NormalizedPointSigns318, the identical composite base map becomes an abbreviation; explicitly typed radical-square and curve lemmas unfold that map before the point constructor is elaborated. The involution curve law is similarly given its own typed lemma. Strict-module definitional-equality transparency is enabled and diagnostics remain on, with the unchanged finite1,000,000 heartbeat limit. Root elements, normalized coordinates, nonzero premises, point constructors, group map and all downstream mathematical statements are unchanged. Exact failure evidence remains with the tested91r2 predecessor. This is a proof-boundary repair attempt, not a claim that the timeout is solved; hosted validation is required.
