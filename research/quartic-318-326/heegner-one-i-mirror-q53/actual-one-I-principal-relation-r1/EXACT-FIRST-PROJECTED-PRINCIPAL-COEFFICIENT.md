# A principal divisor with nonzero coefficient at the smallest faithful ideal orbit

The field, line, odd character λ, and twist d are exactly those of
the [reviewed explicit line tower](../actual-one-I-explicit-line-field-r2/EXACT-LINE-TOWER-AND-DISCRIMINANTS.md).
Take the actual integral line generator

    B = (1/2d) sum_{k=1}^6 x([k]P)

and the literal integral element a = W−169B = 169(y(P)/d−B) in F.
The sum over k represents the same six sign pairs as the doubling
orbit. We compute its first projected divisor coefficient and
principal norm, not its full ideal factorization or a bound on
the faithful class rank.

## The norm-3 orbit has a nonzero coefficient

At 3 the curve has split Tate parameter Q with v_3(Q)=2.
Choose one nonformal point-field prime w and identify P with a
choice of T=Q^(1/13) under the Galois-equivariant Tate
uniformization. This is one of the twelve norm-3 primes in the
free relative orbit: the transvection inertia is transitive on
all choices of T above each prescribed nonzero quotient coordinate.
The labels [k]P, k=1,…,12, are the distinct relative prime addresses.
Normalize the ramified valuation at w to v(3)=13, v(T)=2.
A minimal change from the Tate coordinates has the form

    x = U² X + R,       y = U³ (Y+X/2),

where U∈Z₃× and R∈3Z₃ (the latter follows from the location of
the ordinary node after reduction). Choose the sign of the Tate
isomorphism so U≡1 mod3. This is a choice of representative of
the free orbit, not a change in a.

The Tate formulas for X(T^k),Y(T^k), as in Silverman,
*Advanced Topics in the Arithmetic of Elliptic Curves*, V.§3,
have n=0 terms T^k/(1−T^k)^2 and T^(2k)/(1−T^k)^3.
For 1≤k≤6 the remaining terms, including their constant q-sums,
have valuation at least 26−2k≥14. Consequently

    v(x([k]P)) = v(y([k]P)) = 2k       (1≤k≤6),
    dB = (U²/2)(T+3T²) mod valuation ≥6,
    y(P) = U³(T/2+2T²) mod valuation ≥6.

For the second equality, the T² coefficient in the X sum is
2 from X(T) plus 1 from X(T²); R contributes at valuation ≥13.
For the third, X/2 contributes T/2+T², and Y contributes T².
Thus the T coefficient of y(P)−dB vanishes mod3 and has valuation
at least 15 after multiplication by T. Its T² coefficient is a
unit since U≡1 mod3. Therefore its exact valuation is 4.
The opposite point has valuation 2 for this difference (its
T coefficient changes sign on the y term). All other sign pairs
have valuation 2, since dB has that valuation and their y
coordinates have larger valuations. The factor 169/d is a
3-unit, so these assertions hold for the conjugates of a itself.

Write eλ=(1/12)∑k k⁻¹[k] in F13[Δ]. At the chosen w, the
literal coordinate of eλ div(a) is therefore (4−2)/12=11 in
F13. Equivalently it has coefficient 2 on the projected generator
eλ w of this free orbit. Baseline valuation 2 on the full
orbit contributes zero. The other primes over 3 are the formal
ones with nontrivial relative stabilizer and contribute nothing
in the λ projection. This is a concrete principal relation with
nonzero norm-3 coordinate, even though its other coordinates
must still be determined.

## Exact principal norm and unresolved support

Taking the point-field norm by the sign involution gives
169² B²−13 d v(v−13)(v+39). In the untwisted x generator u=v/13
this is 169²(B²−d·u(u−1)(u+3)). Its absolute norm from degree84
is the resultant against the monic x polynomial after
evaluation in the degree-84 quotient. The replay uses modular
composition there to construct B, followed by the Euclidean
resultant recursion and certified CRT. The exact archived complex
bounds |v|<1456 and |B|<336 give the uniform absolute norm
bound

    ((169·336)^2 + 13 d·1456·1469·1495)^84.

The CRT product exceeds twice this bound; a fresh prime verifies
the centered result independently. The script verifies the gcd
resultants at all four small good free-orbit rational primes
53, 59, 73, 83: the element vanishes at none of their point-field
prime reductions. It also removes every rational prime less
than 200000 from the exact absolute norm and reports the remaining
integer as **unfactored**, not prime. A norm factor is only a
candidate ideal support until the local factors and the λ
weights are computed.

A completed principal row would give a relation eliminating the
norm-3 generator from a certified factor base containing all its
other projected support. A nonzero norm-3 coefficient alone
does not imply that class is zero, does not certify generation,
and is not a global S-powerclass for the current local Selmer
matrix. The exact remainder is a concrete arithmetic next
obligation rather than a hypothesized factorization.
