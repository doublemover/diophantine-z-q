# An independent odd-prime separator and the literal descent-field sizes

Use the same actual fixed one-I base d=2811626664334219040035976315
and E_d. This is a bounded source audit, not an actual odd Selmer
bound or an assumption about finiteness of Sha.

## What would separate rank zero from divisible 2-primary Sha

At 13 the literal curve is good ordinary: d≡1 mod13, the exact point
count is 16, and a13=−2. The same mod-13 full GL₂ image as in the
[fixed residual calculation](../actual-one-I-galois-no-seed-transport-r1/SAME-RAY-FROBENIUS-IS-FREE-BUT-NOT-THE-THETA-SEED.md)
holds on E_d. One can use its irreducibility after character twisting,
together with its split multiplicative Tate uniformization of depth 2
at 3. The two transvection lines again give SL₂ and the determinant
is onto. Its rational 13-torsion is therefore trivial.

A **certified upper bound dim Sel₁₃(E_d/Q)≤1** would now be sufficient,
with no Sha condition. The actual root number is negative, and
[Dokchitser–Dokchitser, Theorem 1.3](https://annals.math.princeton.edu/2010/172-1/p11)
makes the full 13∞-Selmer corank odd. The map from finite Sel₁₃ onto
the 13-torsion of full primary Selmer (since rational 13-torsion
is trivial) bounds the corank by the finite dimension. Thus that
single finite upper certificate would give s13=1. The published
[Yan–Zhu, Corollary 1.4 and Theorem 5.11, final v4](https://arxiv.org/html/2412.20078v4#S5.SS3)
then gives analytic rank one at this good ordinary prime; Gross–Zagier–
Kolyvagin gives rank one and finite Sha as a **conclusion**. Only
the rational, not the integral, corank-one result is needed.

Even the known auxiliary is compatible with that route:
m=1506119 is prime to 13 with m≡4 (mod13), so 13 splits in Q(sqrt(−m)).
The same K splits all old bad primes by the prior exact checks, and
the complementary twist has analytic rank zero by the certified
even Cassels result and the independent rank-zero 2-converse.
Thus the auxiliary's 13-primary corank is zero by the forward
Kolyvagin theorem. Its ramification at 97 and 15527, outside the
bad support and 13, also proves it is disjoint from the 13-torsion
field, so the residual restriction remains absolutely irreducible
on that specific K. This gives a concrete same-base optional
auxiliary, not the missing computation of dim Sel₁₃.

The naive nonzero 13-division-point algebra is a field of degree 168:
GL₂(F₁₃) acts transitively on all 168 nonzero points. Away from 2,3,13,
at every prime dividing d its inertia is scalar −I, since E_d is
the ramified twist of the good original curve there. Every orbit
on nonzero vectors has size 2, so every prime of the point field
over such a rational prime has tame index 2. Its absolute discriminant
is therefore divisible by d^84, over 2300 decimal digits. This is
a concrete size of a standard descent route, not an impossibility
claim about a cohomological certificate exploiting the projective
action or new trace methods.

## The smaller standard 3-subgroup route is unavailable

The actual 3-division polynomial after x=d u, removing d^4, is

```
3u⁴ + 8u³ − 18u² − 9.
```

It is irreducible modulo 5 after dividing the leading coefficient:
the monic reduction has gcd 1 with u^25−u. This proves the absence of
a rational cyclic 3-isogeny, not a non-vanishing statement. In generic
full 3-descent the field of a nonzero 3-point is Q(u,w) with
w²=d·u(u−1)(u+3), using w=y/d. The literal monic equation for v=3u
is v⁴+8v³−54v²−243, with discriminant −2^16 3^13, and the norm of
u(u−1)(u+3) is −768. All primes in d therefore have valuations
exactly one in the latter radicand over Q(u). This quadratic
extension is genuinely degree two and ramifies tamely at every
prime over each of them. Thus the degree-eight 3-point field's
discriminant is divisible by d^4 (110 digits for d^4 alone). The
computable generic procedure is [Schaefer–Stoll, explicit §10](https://www.mathe2.uni-bayreuth.de/stoll/papers/p-descent-long.pdf),
requiring certified relevant class group and S-units and true local
Selmer conditions, not merely the small quartic projective field.

A genuine rational point obtained from a 3-cover would of course
separate the two cases immediately. A bare abstract 3-Selmer
dimension cutoff would instead need an independent rank-one
3-converse at the actual split multiplicative prime 3 or an
arithmetic nondivisibility certificate. The
[Castella multiplicative theorem](https://web.math.ucsb.edu/~castella/Multiplicative-pconv.pdf)
requires p>3; it does not supply that implication. Knowing the
dimension of an odd Selmer group is not by itself a proof of
finiteness of its Sha quotient.
