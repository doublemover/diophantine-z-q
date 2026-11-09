# Constructed Lucas labels and adjustable scalar preparation

Status: pending hosted Lean check and distinct bounded source review. No local Lean compilation/build. This100-source packet is not a complete proof of the318/326 arithmetic theorem.

## Source comparison

The primary historical completeness argument, `docs/sources/quartic_v10.tex` subsection `subsec:v9-completeness`, chooses a positive scalar index s divisible6, sets a=s+1, and takes a positive odd Lucas pair at index2(a−2), before fixing real neighborhoods and choosing contact primes. The currently retained `LucasWitness318.source_positive_odd_witness` proves precisely the required integral equation and parity using `positive_odd_witness_at_index`, `U_mod_two`, the exact Lucas invariant and divisibility modulo a−2. Its full statement and proof were read for this application.

The actual318 input is not the older2X²+3 source. `docs/arithmetic.md` identifies the final beta as3723(2X+1)². This is the beta used here; its exact affine relation is beta−3723=14892(X+X²).

## Adjustable local choices

For arbitrary natural A≥6 and B≥0, define R=2^A*3^B and modulus6R. A natural h congruent to R modulo6R has the exact expression h=R(1+6j), for a natural j, hence v₂(h)=A and v₃(h)=B. It is nonzero, even and divisible64. Thus the earlier restricted choice of depths6 and0 is no longer imposed.

Before any real/contact choice, choose positive d and set the second label to1+6^(A+B+15)*d. Its translated index is even and has both2/3 depths at leastA+B+15. Consequently the predecessor's genuine actual scalar unit criteria are satisfied: v₂(n−1)≥A+15 and v₃(n−1)>B. These are the actual chart norm and half-trace leaves, not substituted scalar variables.

`label_arbitrarily_divisible` proves that d can impose any further fixed natural divisibility on the translated index and any prescribed size lower bound. This preserves flexibility for the still-open other-prime and Anchor producers; it does not prove those producers.

## Actual four-label producer

`FixedArithmeticLabels318` constructs labels

- n=3723(2a+1)² for the original integer input a;
- the scalar label s=1+6^(A+B+15)*d;
- t and z from the actual retained positive odd Lucas witness at parameter s.

All four are positive and odd. They satisfy the exact integer detector relations n=beta and t²−s(s−2)tz+(s−2)²z²=1. No Lucas pair or nonzero-label hypothesis is left for the caller. The actual chosen values are retained through the signed coherent charts and all downstream assignments.

## Same-h final consumer

`PreparedLucasSource318.current_source_prepared_lucas` constructs these labels before the eventual rational contact threshold t and before all CRT data. The original continuity modulus must explicitly contain6R and the initial residue must be congruent toR modulo6R. The original mixed CRT gives the same final h, whose exact2/3 depths produce both actual scalar W units.

The theorem retains the same input, contact parameter, fixed signed roots, real scalar bound, pole inputs190/241/292 and scalar pole through the literal full288-row current-scale HasSolution. Its conclusion also exposes all four positive odd labels and the two exact integer detector equations. The all-other-support-prime leaf hypotheses still imply the reduced scalar denominator is a square and give the exact4/2/2 pole valuations. Actual local squares at2,3,17 are carried unchanged.

Still open are the other scalar support-prime preparation, three detector local preparations, compatible simultaneous prime/ray pattern, four actual simultaneous two-twist rational-point realizations, and final ternary Anchor. The constructed integer relations are not themselves a prime-selection theorem. Adjustability ofA,B andd is not a proof that all remaining local conditions can be realized simultaneously.

## Evidence

97 sources are byte-identical copies of `forward-scalar-index-preparation-r2`; three new modules have finite1,000,000 heartbeat limits. There are137 baseline dependencies, including the actual Lucas producer chain. The inherited normalization proof-boundary diagnostic repair remains pending hosted verification. Symbolic checks verify the exact Lucas invariant, source relabeling and beta relation; finite residue/Lucas tests are sanity checks only. Source-policy/dependency and audit checks are structural, not kernel or whole-proof acceptance.
