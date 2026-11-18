# Nine mutually compatible indexed positions at a single new shared grid

For the same literal model labels (−1,−1,−1,−1), roots, scale convention
and shared denominator 17294016221357051154 as the reviewed cross-row
packet, take the **new** parameters

    u=10000000000000000002018987660553779409060163799522482685314202437075281,
    w=2026304932131480.

With the usual merged indices [0,1,2,3,4], [0,5,6,7,8],
[0,9,10,11,12] (index 0 is the common zero slope), exactly
[0,2,5,6,10,11,12] are prime. All seven simultaneously satisfy p≡1
mod816, (p/7)=−1, z⁸=−1 and t⁴=2 in F_p. All six other distinct
values have supplied proper factors. The seven give nine indexed
positions, namely row0:[0,2], row1:[0,1,2], row2:[0,2,3,4].

For the literal signs of R_r=(1+r,2r) on y²=x³−(3−r)²x, exactly two
orientations meet the three CRT conditions with Π the product of all
seven primes, L=16, h₀=0. One fixes the minus signs in the reported
root order as [0,1,1,0,0,0,0]. The 2419-digit h in the data satisfies
h=0 mod Π³M−, h=1 mod M+, h=0 mod16 for the corresponding true order
LCMs, by checked annihilator divisibility. All indexed copies of 0 use
the same sign.

The stdlib checker is copied byte-for-byte from forward-cross-row-
frontiers-r1; its self-contained method and proof apply unchanged.
All 202 recursive Pocklington nodes and every composite divisor are
replayed. Annihilator guesses are accepted only after actual Jacobian
point multiplication. The certified overlap-only screen needs just
primes 2,3,5,61,16073 (maximum factored gcd 1028672; 76 scalar-strip
tests). All 3⁷ skip/sign choices, embedding the sample in its actual
shared grid, are checked. Run python3 -B verify.py and compare with
FINITE-REPLAY.json. The signed choice, moduli and digits belong to this
one parameter, not any union with another sample.

This improves an actual single-parameter linked compatibility count
from six to seven distinct primes and eight to nine indexed positions.
It does not improve the separate 11/15 all-prime count, supply a whole
15-position Values structure, identify these labels with any prescribed
integer input, control arbitrary prescribed L,h₀, prove the Gaussian
prime theorem, or execute Lean.
