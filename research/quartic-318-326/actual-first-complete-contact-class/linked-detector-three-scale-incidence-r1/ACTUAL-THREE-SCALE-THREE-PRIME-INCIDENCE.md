# One actual h,t has simple nominated odd contact in all three literal scales

This is a positive **three-row finite incidence** in the original
detector construction for a=0. It preserves exactly the same J
and original four labels from 5a70adc6 and a7dd144b. There is
one explicitly certified new h and a common square contact t
such that, at three assigned good split primes, the actual
stored pole of the assigned row has valuation one:

| original slot | p | primary root, full order | opposite root, full order |
| --- | ---: | --- | --- |
| 190 | 3162001 | 2389553, 98746 | 772448, 791033 |
| 241 | 3641809 | 828425, 37974 | 2813384, 909529 |
| 292 | 4247281 | 4060409, 26570 | 186872, 1060841 |

Across these three selected primes, each p contacts exactly
the one assigned row, not the other two. None of these facts
implies the absence or suitability of any other odd contact
of the same t. There is no complete PointPair claim.

## Actual scale residues from the original labels

The same s=1+6^15·3^65536 J and k=2(s−2) give the literal
labels (3723,s,U_s(k+1),U_s(k)/(s−2)), as in the checked
fixed scalar prefix. Nothing here substitutes a congruent
but different integer label as the source datum.
At each p the finite order certificate in both split arms
is by explicit multiplication and all prime-order-divisor
tests. First-return formal parameters mod p² are nonzero.

For the scale calculation in either arm, a point order
o mod p gives an exact period dividing p·o mod p²: the
first formal residue kernel is killed by p. Thus reduce
the enormous labels modulo p·o, using exact Lucas doubling.
To divide U_s(k) by s−2 modulo q=p·o, remove its full
q-supported denominator part g and compute U_s(k) modulo
qg; after dividing by g, the remaining denominator is a
q-unit. The unchanged label recurrence and beta/Lucas
equations are checked at these moduli as controls.

The resulting charts U([n_i]R) are all units in both arms.
Multiplying −1/U([n_i]R) over all four indices gives the actual
two product residues. Its trace half and norm give the
original c_1,c_2. The exact scale triples mod p² are

| p | (c_0,c_1,c_2) mod p² |
| ---: | --- |
| 3162001 | (1,1786048908309,7488794411044) |
| 3641809 | (1,1854251916702,12702581475132) |
| 4247281 | (1,8401966907874,3289448256468) |

Every scale is a unit and all twelve nonzero scaled
roots θ_i/c_j² are distinct mod p at **each** of these p.
Thus each selected p avoids the entire explicit fixed
saturation integer B in f0016ec0, including the cross
determinants; root zero is disjoint as well.

## One t CRT and one independent h CRT

For row j at its p let z_j be the listed lift with
z_j²=−1+p mod p². The checker supplies r/d=z_j/c_j mod p²,
using the exact scale residue above. Then T_j=c_j²t
has T_j+1 of exact p-depth one, its other four factors
and its Δ are units, and all five factors of each
other scale are units. The actual contact values at
all three scales are printed mod p².

These three numerator residues are compatible with any
denominator d=B^N, N>=2, and r=1 mod B, by ordinary CRT.
They remain exact as r is made arbitrarily large.
The supplied small numeric test d=204 and its exact r
certify the same three local calculations more compactly;
d=204 lacks 2399 and is already excluded as a full witness
by the universal denominator theorem. It does not replace
the compatible saturated denominator choice.

For the index use h=h_old mod the exact protected L
from 53291d8a, maintaining its finite scalar precision
rows, and for each listed prime impose h=0 mod its
primary full order, h=1 mod its opposite full order,
and h=p³ mod p^4. The one generalized CRT (not three
independent h) is run and rechecked for all three primes.
The least positive index in its residue class is already
a certified real center: outward 16384-bit rational dyadic
group arithmetic gives

    N(U([h]R)) in
    [2078392885987825125,2078392885987825126] / 2^64.

This is strictly above the necessary absolute 1/100
margin. The same h modulo 5 maintains the original four
nonzero guard residues, and the earlier protected L
keeps the specified finite old scalar rows at fixed J.
It does not keep the exact earlier scalar value or
its unseen support when h varies.

## Local folded-pole conclusion and scope

At each p the original strong one-place formal-entry
hypotheses hold with Pi=p, and the two listed full
orders as Mminus and Mplus. The pointwise source
argument of 1beafde5 therefore applies at this same
h and t to its assigned scale: construct the primary
chart, eight norm/comparison bounds and sixteen
weighted positive leaves on that arm, use literal
opposite parity, and obtain a unit rational trace
quotient. It uses the exact weight valuations
−1,−7,−25 and the original fixed scale, not any
unproved all-prime pattern. Hence the stored
pole valuation is exactly +1 there.

If choosing the symbolic d=B^N, the known fixed-index
real and small-place open-region estimates can separately
be met by taking N sufficiently large and then r large
on the same numerator progression. They do not remove
unlisted odd support or imply rational points. This
certificate gives a genuine common three-row finite
positive incidence, not complete square denominators,
all four realizations, or a Lean declaration.

    python3 -B check_actual_three_scale_incidence.py | cmp - EXACT-THREE-SCALE-INCIDENCE.json
    sha256sum -c SHA256SUMS

The replay pins the old prefix, singleton L, modular
group and real interval arithmetic by exact bytes.
There is no prime search or network input in replay.
