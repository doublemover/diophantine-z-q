# A one-power dyadic test for both original signs, with a guaranteed odd side

Let p be a rational prime, p≡1 mod 8. For each of the two roots r²=2
in F_p, put d=3−r and let R_r=(1+r,2r) on E_d:y²=x³−d²x.
The models are nonsingular: (3−r)(3+r)=7 and p≠2,7.
Write χ for the quadratic character. Define the test

    H(p):   2^((p−1)/4) = (−1)^((p−1)/8) mod p.

**Theorem.** For either sign, H(p) is equivalent to R_r belonging to
2E_d(F_p). If H(p) fails, both signed orders are even. If additionally
χ(7)=−1, H(p) is equivalent to *at least one* signed order being odd.
On success the root r with χ(3−r)=−1 always has odd order, and that
root is determined by quadratic characters alone. The other can have
either parity. No CM formula, order factorization or curve-point search
is required by this test.

Thus on any list of such mixed-7 primes that pass H, orient the guaranteed
odd root as plus at every position to make the entire plus-order LCM odd.
Repeated positions cause no dyadic problem. In particular this clears the
2-part of gcd(Π³ M−,M+) and the dyadic requirements for L=16,h0=0. It
does not clear their odd-prime parts or necessarily give the orientation
that can clear those parts. If both point orders are odd, discarding the
other orientation could wrongly preclude a solution. Failure at even one
prime here obstructs every orientation, even if χ(7)≠−1. These are
conditional statements about candidate primes, not a fifteen-prime witness.

## 1. Calculate the character of x(R) for either sign

The values χ(1±r) agree, because their product is −1, a square here.
In F_(p²) take a primitive 16th root ζ; 16 divides p²−1. With
r₀=ζ²+ζ⁻² and s=ζ+ζ⁻¹, one has r₀²=2 (ζ⁴+ζ⁻⁴=0) and s²=2+r₀.
Moreover r₀ belongs to F_p since ζ² is fixed by Frobenius, and
s≠0. The p-th power of ζ is ζ if p≡1 mod16 and −ζ if p≡9 mod16,
and respectively s^p=s or −s. Thus χ(2+r₀)=s^(p−1)=(−1)^((p−1)/8).
Euler's criterion gives χ(r₀)=2^((p−1)/4) since r₀²=2. Taking
characters in 2+r₀=r₀(1+r₀) proves χ(1+r₀)=1 exactly for H(p).
The other sign has the same character as already shown. In particular
p≡9 mod16 requires a NONquartic residue 2 rather than a quartic residue.

## 2. A character detects doubles, not generally odd order

If R_r=2Q, Q is affine and y(Q)≠0. The duplication identity on E_d

    x(2Q)=(x(Q)²+d²)² / (4 y(Q)²)

forces 1+r to be a square. Conversely if a²=1+r, then a≠0. Put
u=a+r/a, x=1+2r−2u, y=−2+10r−(r+4)u, m=2−u. Direct substitution
using u²=5r−1 gives y²=x³−d²x, 2ym=3x²−d², m²−2x=1+r and
m(x−(1+r))−y=2r. If y=0 then d²=3x² and x³−d²x=0, forcing
x=d=0, impossible. Hence (x,y) actually doubles to R_r. This is the
existing original BranchHalving.half_parameter / explicit_half
construction; the new step is the exact signed ray character and
odd-order selection, not the explicit half. Every odd-order group
element is a double, so failure forces both even.

## 3. The quadratic twist parameter identifies the odd-order side

For any double Q'=2Q other than O, every nonzero x(Q')−e, for
e=0,d,−d, is a square. Indeed translate X=x−e so the curve is
y²=X³+B X²+C X. The tangent identity gives
X(2Q)=(X(Q)²−C)²/(4y(Q)²) in each chart. When χ(d)=−1,
none of (0,0),(d,0),(−d,0) is a double: in each case choose e
with nonzero difference ±d, which is a nonsquare. These are all
nonidentity points killed by 2. Thus no point has order 4; the
2-primary part of E_d(F_p) has exponent 2. In this finite abelian
group a point is a double exactly when it has odd order. This proves
the claimed equivalence on the nonsquare-d side; χ(7)=−1 ensures
there is exactly one such sign.

For comparison, if χ(d)=1, all three nonidentity two-torsion points
are doubles. Here is a direct construction: in the translated equation
at e, write y²=X(X+a)(X+b) with a=e−e', b=e−e''.
Because χ(−1)=χ(2)=χ(d)=1, write a=s² and b=t² (both nonzero).
Put X=st, y=st(s+t). Then y²=X(X+a)(X+b), y≠0 since s=−t would
give a=b, and X²=ab=C. The duplication formula gives X(2Q)=0, i.e.
2Q=(e,0). Every such point has four halves since the kernel E[2] has
four points. It follows E[4] is rational; in particular 16 divides the
group order. Moreover a point which is not a double has order divisible
by 4 (otherwise its odd multiple of order at most 2 is a double, and
its difference from that multiple is a double). This latter observation
does not supply the missing odd-prime conditions.

## 4. Exhaustive small-prime replay, separately from proof

Run python3 verify.py and compare with FINITE-REPLAY.json. It enumerates
every point and double of both actual curves for all 129 primes p≡1 mod8
below 4000, and repeatedly adds R to obtain its actual order. Of 69
mixed-7 primes, 35 pass H and 34 fail. For p=41 (9 mod16) the two orders
are 13 and 4; for p=761 they are 181 and 5, so the guaranteed sign need
not be uniquely odd. For p=953, H passes but χ(7)=1 and both orders are
even (58 and 116): the added hypothesis matters.

The existing positive-root halving route uses z^8=−1 and t^4=2;
these imply H on its p≡1 mod16 ray. This packet also covers the
complementary 9 mod16 case and reverses the halving implication on the
whole 1 mod8 ray. Mathematical source/replay only, not Lean acceptance,
global order coprimality or a realization of the selected affine input.
