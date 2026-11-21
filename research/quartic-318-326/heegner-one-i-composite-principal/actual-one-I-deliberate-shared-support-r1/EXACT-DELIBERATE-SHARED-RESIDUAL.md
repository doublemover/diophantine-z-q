# Exact shared composite support for a second faithful principal divisor

Use the same actual one-I d, fields, point, and character from the
[reviewed factor-free relation](../actual-one-I-principal-composite-r1/EXACT-FACTOR-FREE-PRINCIPAL-IDEAL-RELATION.md).
Write a=W−169B, C for its exact 2379-digit residual norm, and I_C
for the entirely known supported ideal over C. Let q₃,q₅₈₈₁ be the
same oriented local generators as in the preceding row.
The new element is not a second unrelated large-norm sample:

    D = 3·5881 = 17643,
    R = 1+(W+169B)/D,
    b = a R = a + (W²−169² B²)/D.

Thus b was chosen to share a's residual support. We certify the
entire shared multiplicity, and the other two known coefficients
cancel in the faithful projection.

## No primes above C enter the ratio

Let B=N_B(u)/D_B(u) in the prior exact division polynomial notation.
The code checks by monic Euclidean division over Z/C that f(u)
has gcd one with D_B(u), and with

    H_D(u) = (D·D_B(u)+169·N_B(u))²
               −169² d·u(u−1)(u+3) D_B(u)².

Every division uses a unit leading coefficient. Reducing this exact
calculation modulo any rational prime p dividing C still gives
gcd one. At a point-field prime above p the denominator D·D_B is a
unit and the two possible signs of W are controlled by H_D; hence
D+W+169B is a unit at **every** such prime. This is stronger than
testing the single residue homomorphism defining I_C. It proves

    div(b)|_(primes over C) = div(a)|_(primes over C) = I_C

in multiplicative ideal notation, with every exponent retained.
No factorization, squarefreeness, or primality of C is presumed.

## The two exact local changes

At 3 the denominator D has normalized valuation 13 on the free
relative orbit. The numerator W+169B is the negative of a with
P replaced by −P, so its valuations there are 2 except the last
opposite label, where the valuation is 4. Both are <13. Thus
the 12 values of R are −11 except the opposite label, with −9.
The uniform −11 gives zero in λ; the opposite label contributes
−2 on the eλ q₃ basis, canceling a's coefficient +2.
All other 3-orbits have nontrivial relative stabilizer.

At 5881 the exact old norm had valuation one. Thus W+169B is
a unit at every prime above 5881 except the opposite of q₅₈₈₁,
where its valuation is exactly one. The degree-one lifted root
at that opposite prime is calculated modulo 5881²; it gives
(W+169B)/5881 = 1334 mod5881, and R = 2406 mod5881, nonzero.
The rational denominator therefore contributes −div(5881),
killed in λ, and one positive correction at the opposite prime.
As λ(−1)=−1, R has coefficient −1 on eλ q₅₈₈₁, canceling
a's +1. This is the same labelled generator, not a permuted
cohomology representative. At 13 both primes are fixed and
their divisor components never enter λ.

Consequently the projected principal rows of a and R are
linearly independent modulo 13 as **divisors**. Indeed a has
nonzero projected C-supported divisor by the prior norm-power
test, and R has none there; nevertheless R has nonzero q₃
coefficient. Equivalently b and a are two such independent rows,
with the same C-supported part and zero q₃/q₅₈₈₁ part for b.
Their difference removes I_C completely and preserves both
explicit known coefficients. Thus shared composite cancellation
is actually possible; it does not require factoring C.

This proof does not certify new support of R outside the listed
places, a smooth complement, or generation of the faithful
class quotient. In particular one cannot deduce a class-rank
upper bound from these two independent principal divisors.

    sha256sum -c SHA256SUMS
    python3 -B check_deliberate_shared_support.py | cmp - EXACT-DELIBERATE-SHARED-SUPPORT.json
