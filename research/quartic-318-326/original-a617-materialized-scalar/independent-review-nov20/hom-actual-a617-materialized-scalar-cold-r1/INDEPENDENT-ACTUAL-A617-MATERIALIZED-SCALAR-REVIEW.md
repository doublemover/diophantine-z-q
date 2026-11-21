# Independent cold review: the materialized original a=617 scalar

**PASS, exact paper and arithmetic replay.** The following SHA-256 digests identify the reviewed author bytes:

| File | SHA-256 |
|---|---|
| `SHA256SUMS` | `a8fcafe0371e31153e30f96dd218e7e917018205fb2fb95da449c33535c85ce5` |
| `ACTUAL-MATERIALIZED-A617-SCALAR.md` | `6fe942f3ff51e420cdf6cf1bf29b563e7b6a4e342465cb063d61c384167571d3` |
| `EXACT-MATERIALIZED-A617-SCALAR.json` | `7f22536b2da38e57de106f7ea63c0ed10226144d78ec2ec09fdfbbb82d10d8af` |
| `check_materialized_a617_scalar.py` | `584c1d249233da55b56ee9f6013a2d0661e114a7740ac2b7a5ce095e48448e8c` |

I verified the manifest and ran the author's checker, producing exactly the frozen JSON bytes. This replay checks the annihilating multiples, separately at each split residue arm; they need not be minimal, except that the small guard order at 59 is independently exactly 60. I rederived the guard by sequential additions over the explicit field with 59² elements, separately from the checker's finite arithmetic: the actual label residues are (15,1,59,1) modulo 60 and the four coefficients are (8,32,32,32). These certify the single set of literal `RealGuardTrace318.guardValue` inputs at the displayed h, not four independently chosen evaluations. I checked the modulus-six recurrence, the exact integer division of the last Lucas label, and that the displayed i really is the one producing the fixed label s=1+i.

The interval has both endpoints negative and even its closer endpoint has absolute value strictly greater than 1/100, by integer comparison with 2^64. This is the absolute norm guard in `PreparedIntegerSource318.scalar_domain`, not a claim that the norm is positive. The lower and upper endpoint 0<b<17 thus apply to the one literal `scalarB` value for this tuple.

At each printed odd prime, annihilation and the extra p-power give twice the formal depth greater than v_p(R), including the squared factor at 359. The unramified logarithm is valuation-preserving on the odd formal group, so 2v_p(i/h)-15v_p(R) is the exact valuation of Q. At 2 the actual dyadic chart applies (v_2(h)=7); it gives coefficient depth and the same norm difference without using an odd-prime logarithm. Consequently the *actual* W is congruent to one on the first support: it was not replaced by W=1 in the definition. The 2/3/17 square/depth guards and unit delta residues 2,4,46 at 5,13,47 agree. The nonsquare test at 5 proves that the exact delta is not globally square, not that its numerator has been factored.

**Scope.** This is one admissible original scalar component, specified by explicit h, J and a compact formula for i, its Lucas labels and b. It is not expansion of the rational numerator/denominator. The separately checked degree-two graph provides a receiver for this scalar; its all-place local statement uses full first-support preparation. No rational graph point, specialized global root sign, rank, scalar point pair, anchor, or common index completing the three detector poles is established here. No Lean kernel invocation was made.

Signed: independent review, 2026-11-21.
