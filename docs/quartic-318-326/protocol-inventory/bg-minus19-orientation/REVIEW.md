# BG Proposition3.9: the remaining −19 numerical orientation

Date: 2026-11-08. Reviewer: `/root/restart_modular_curve`. Runtime model identifier was not exposed. This is a source/application audit of the remaining numerical predecessor, not a new repair of the CM-order or orbit arguments. No shared edits, Lean compilation or primary-source correction claim.

## Result

The final published source explicitly claims a numerical calculation with controlled error. It does **not** display its computed value, an error enclosure, or the concrete evaluation data needed to replay that calculation. The historical retained geometry audit records the resulting normalization but does not reproduce such a certificate.

I verified the exact embedded order, an explicit upper-half-plane representative in a declared real embedding, the modular normalization and the two widely separated candidate values. I have **not** independently evaluated the automorphic function with certified errors. Accordingly the source statement is a reported controlled computation, not mere empirical evidence, but this new numerical-review obligation remains **open**, not disproved. The degree-four map repair or CM-orbit count alone does not discharge it.

## Primary source actually read

Baba–Granath, Canadian Journal of Mathematics60(4)(2008),734–757, DOI https://doi.org/10.4153/CJM-2008-033-7. Final PDF SHA-256 `c711b2bed2aa0dd70d1bc1dd06c6d4a921c4b8735452bc143431f080a8cac12c`.

I read the actual published Proposition3.9 on p744 visually and as text, the definitions of h4,h6,j_m and their normalization on pp740–741 (freshly rendered), the real/quaternionic setup, and AppendixA pp755–756. The historical `parallel-geometry-report.md` A001 was read first for its scope. It states that preprint Proposition10 fixes the coordinate; it contains no numerical output, truncation order or error estimate for the −19 value. A bounded search of that report, `height-whole.md`, the retained applications inventory and final height merge report did not identify a separate numerical replay. This is not a claim that no unpublished author calculation exists.

AppendixA proves a general Hilbert modular restriction method. The introduction says the relevant curves can be embedded into the Q(√5) Hilbert surface and Eisenstein series can compute their modular forms to arbitrary precision. For this particular value, the paper does not specify the concrete β/embedding, the chosen restricted generators or linear combinations, the series cutoff, the tail majorants or the resulting interval. Its general method explains a possible route but does not provide an already replayable certificate at the precision of this audit.

## Actual order and representative

The source's order is Z[α], where α=i+(1+3j)/2, with i²=2,j²=−3,ij=−ji in B6. Its reduced trace is1, norm5, and

α²−α+5=0, (2α−1)²=−19.

Moreover α=−1+i+3(1+j)/2 belongs to the source's maximal quaternion order. Thus the quadratic order has discriminant−19. Contact's separate lane owns the optimal-embedding/CM-orbit identification and the full Atkin–Lehner action; this packet does not infer that identification from a numerical quadratic field alone.

In the real embedding used in the historical polarization check,

i ↦ diag(√2,−√2), j ↦ [[0,−√3],[√3,0]],

α acts by [[1/2+√2,−3√3/2],[3√3/2,1/2−√2]]. Its upper-half-plane fixed point is

z19=(2√2+i√19)/(3√3), with |z19|=1.

This follows by solving 3√3 z²−4√2 z+3√3=0. Here the italic i in the complex coordinate is the complex imaginary unit, not the quaternion generator. The source does not specify its numerical evaluator's real embedding. Transporting an evaluator to these coordinates requires the corresponding conjugation and automorphy factors; matching a bare complex number is insufficient. The representative for μ=2j+ij in this same embedding is x6=i(1+√2).

## Normalization and the exact separation test

The original p740 normalization is

h4³/h6²(x6)=√−3.

The radical is visible in the typeset page and is lost in some text extraction. It is not the normalization with value−3. The definition on p741 is j_m=4h6²/(3h4³), hence F=j_m² satisfies F(x6)=−16/27. Squaring removes the irrelevant sign choice for √−3.

Conditional on the preceding source geometry and repaired CM identifications, Proposition3.9 has exactly two possibilities:

j=F, or j=256/(729F).

At the actual −19 point, its separately computed algebraic j-value is81/64. Therefore

F(z19)=81/64, or F(z19)=16384/59049.

These are approximately1.265625 and0.2774644786533218. Those decimals are evaluations of the two exact rational candidates, **not** computed values of the modular function. Their exact gap is3734393/3779136. In particular

16384/59049 < 1 < 81/64,

with margins42665/59049 and17/64. Thus a correctly normalized certified enclosure proving Re(F(z19))>1 would choose the first alternative. For example, an enclosure1<F<3/2 would suffice. This is a deliberately coarse target: recognizing an exact rational to many digits is unnecessary once the two-candidate argument is sound.

For any arbitrary nonzero generators H4,H6 of the same one-dimensional spaces, a scale-independent evaluation can use

F(z)=−(16/27)·H6(z)^4 H4(x6)^6 / [H4(z)^6 H6(x6)^4].

A certified computation must bound its denominator away from zero, control every truncation and rounding error, and use the same embedding and normalized points. The scalar factors of the two chosen generators cancel. The formula states what must be evaluated; no actual interval for it is supplied by this packet.

## Why no numerical acceptance is issued yet

The paper asserts that the required error control was done, but the inspected source and historical audit do not expose the actual enclosure. Repeating its claimed rational value, using the desired j=F identity to evaluate F, or using Lin–Yang equation(2), which attributes the normalized result to BG, would be circular as an independent verification of this orientation. An unbounded floating-point series evaluation would likewise not meet the requested error-control review.

Reconstructing the Hilbert modular evaluator is possible in principle but requires additional explicit source-to-generator and tail estimates. No such evaluator is invented here, and no unsupported numerical value is presented. The appropriate remaining item is a reproducible certified interval calculation (or a separately reviewed exact orientation argument), not another bibliography entry or an assertion that a numerical-looking result must be false.

## Actual consumer and scope

V13 SHA-256 `9db71bbfcefb37db56eabcf40a5f9dd85de9ed58294635da3dbf6d4f5caa8fcd` requires the ordered D6 branch values0,infinity,−16/27 at487–498 and575–598, the same polarized Igusa point at608–618, and its normalized theta comparison at984–1008. Swapping0 and infinity without changing J(u) would not be harmless. This is why the numerical orientation is a real source predecessor of that D6 application.

The current literal318/326 D210 dependency separation remains the bounded finding in receipt `0c61654197ba2dddb25375bab62e0b137742040a11156e000e1ba4d89b42be07`. That source does not require this D6 orientation. Neither this nondependency nor a repair of the displayed degree-four map establishes the current global source arithmetic.

## Nine-obligation status

1. Source hypotheses: final p744 explicitly reports controlled numerical work; the actual enclosure is not given.
2. Constructed object: α and the declared-embedding fixed point checked exactly; optimal CM orbit supplied only by the separately assigned lane.
3. Coverage: one correctly identified −19 point suffices for the stated two-candidate function identity; no arbitrary-point test is claimed.
4. Comparison maps: real embeddings/evaluator coordinates and automorphy transport must match; no untracked coordinate substitution is accepted.
5. Object identity: F is the source j_m², not algebraic j reused under the identity being tested.
6. Conventions: √−3 normalization, the square, reciprocal constant and scale-independent generator formula retained exactly.
7. Local analytic conditions: denominator separation, convergence, truncation and rounding bounds remain to be exhibited.
8. Exceptional cases: the two candidates are finite, nonzero and separated by the exact threshold1; the test assumes the prior two-candidate/CM point identification.
9. Downstream use: D6 orientation acceptance remains open in this new audit; no false-theorem verdict or D210 propagation.

The checker confirms exact finite arithmetic only. Public files exclude source PDFs, images and extracted third-party text.
