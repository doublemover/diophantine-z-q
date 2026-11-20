# Two further exact H primes at the fixed original scalar

This uses h=473592745039516333133760, the same J, labels,
and the literal scalar b from the materialized a=0 bundle e2ef09a.
Let D=b/17=β(C/Z)², H=Z²−βC², θ=sf(1−D). These checks
do not modify the earlier accepted first-lift or local-criterion notes.

For ordinary primes with integral charts and unit chart norm at h,
a bounded finite-field scan evaluates the true compact scalar W
without ever expanding the rational value. It proposes group
annihilators using j=1728 Gaussian coordinates; regardless of the
proposal, it checks annihilation of the actual R in each residue
field before shortening any index. Thus reported rows are exact
even independent of the theorem motivating the proposal.
If chart denominators or the chart norm fail their unit tests,
the scanner marks that place inaccessible. In particular this is not
a completeness claim about divisors even below the scan bound.

Two additional primes were discovered and individually refined
through p² by the exact local affine-ball evaluator:

| p | Exact residue orders of R in its two split places | (1−D)/p mod p | v_p(1−D) |
|---:|---|---:|---:|
| 2470991 | 51479, 308874 | 2223081 | 1 |
| 16782959 | 2097870, 699290 | 13715188 | 1 |

The primes are certified by trial division in the targeted checker.
The reduction of index modulo p times the residue order is
legitimate by smooth good reduction modulo p², and all final
chart denominators and scalar circuit units are verified there.
The exact intermediate chart values and residues are in
ACTUAL-NEW-H-PRIMES.json. Thus the two primes are actual exact
simple divisors of H and are in the squarefree θ. The four
known θ primes are now 131,6551,2470991,16782959. Their product
is 35589230039008870789 ≡13 mod24 whereas θ≡1 mod24, so
at least one additional prime of θ still exists. The previously
plausible partial Heegner field of discriminant −63839 fails
splitting at 2470991, regardless of any further unknown support.

We now evaluate the exact first-lift requirement
    X² ≡ −2ξ (mod H)
at both new prime divisors. Of the previous eight specified ξ,
the first new prime rejects four, and the next rejects two more:

| ξ | 2470991 | 16782959 |
|---:|:---:|:---:|
| −3503229612754 | pass | pass |
| −9213710 | fail | pass |
| 558982886506 | fail | fail |
| 1534192441910 | pass | fail |
| −34546822724285 | pass | fail |
| −3634411 | fail | fail |
| 22777399 | pass | pass |
| 207473585 | fail | pass |

Only ξ=−3503229612754 and 22777399 survive among these eight.
All six failures rule out rational points on those particular
residual quartics, with no rational height restriction.
The two remaining are not asserted locally soluble at the
unseen H primes, and other ξ classes from unseen C/L primes
were never part of this eight-class set.

Separately, no exceptional prime dividing the fixed denominator
1+A_scalar can divide H. Its exactly factored support is
29,181,1346909,70850399941, all to exponent one. At 29 and
181 β is nonsquare, at 1346909 the scalar W is a unit by the
explicit inert chart calculation (residue 429536), and at
70850399941 W, a norm from Q(sqrt(-R_input)), has even
valuation because −R_input is nonsquare. The latter two give
nonzero c-valuation, which precludes H-divisibility because
p∤β. This addresses this finite exceptional set, not all
places the finite-field scan skipped.

The ordinary scan up to 120,000,000 found no other hit on its
accessible support. The targeted verification for the two
displayed primes is independent of that negative scan result.
