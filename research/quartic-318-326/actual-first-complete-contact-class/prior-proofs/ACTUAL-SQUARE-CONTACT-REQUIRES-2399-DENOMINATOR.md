# Every literal square contact needs 2399 in the denominator leg

Keep the original unscaled detector slot190 with its unchanged
guarded h and actual label tuple satisfying the Lucas equation.
Take t=(r/d)^2>2, r,d coprime positive integers, and assume
the nonzero literal pole b has a PointPair. Then **2399|d**.

This is not the earlier Pythagorean subfamily: no condition that
r²+d² is a square is imposed. It is independent of h, the old
retuned modulus, and any finite support cutoff.

## What happens if d is a 2399-unit

Set p=2399, u=r²,v=d² and T=u/v. The original contact is

    F(T)=u (2u+v) (u+v) (2399u−v) (407u+32v)
              / (2·2399·407·d^10).

At this prime a square T, including zero, cannot kill any of the
four nonzero-constant linear factors. The three possible roots are
1199,2398,2004, all nonsquares; the other factor is the nonzero
constant −1 modulo p. These claims are checked exhaustively
in the finite residue field. Thus the exact contact valuation is

    e = v_p(F(T)) = 2 v_p(r) − 1,

always odd. If r is a unit it is −1. The parameter Delta=T−1
is integral, including if it is not a unit. The same
negative-odd parity argument as in the Pythagorean proof applies:
the three literal weights have values 2v(Delta)−e,
32v(Delta)−7e and 122v(Delta)−25e, all odd. At either split
place the fold starts at valuation zero and its sixteen odd or
infinite leaves cannot cancel an even square, so both final
valuations are finite and nonpositive. Their reciprocal trace
has nonnegative valuation or vanishes. Vanishing gives b=0
by total division, excluded. Otherwise
v_p(b)=e+2v(traceQuotient)−6v(Delta)<0 is odd. This is impossible
for the literal PointPair by dd5d6ca1.

If p|r then e>0 odd and Delta is a unit as T=0 mod p, so the
early-eight theorem 63be7c0a applies. At this split prime
the exact two residue orders of the original half-point R
are 300 and 80 (the checker uses direct first-return addition,
not CM counts). The midpoint of each has nonzero x and thus
neither is T0=(0,0). Therefore the order in the quotient
by {O,T0} is still the full order for each arm.

If the primary arm is the one of order 300, [2h]R=O there
requires 150|h. But the other arm requires 80|(h−1).
Their gcd is 10. If the primary order is 80, the analogous
conditions are 40|h and 300|(h−1), with gcd 20. Neither
is possible for any integer h. This rejects the positive odd
case, again without any old h residue. Both branches have now
been exhausted and p|d is necessary.

## Exact scope of saturation

If 2399|d instead, r is a unit, the G3 factor has exact depth
one and all other numerator factors are units. Its one factor
cancels the fixed denominator's one factor, so the exact
contact valuation is −10 v_p(d), even. This repairs this
single-place parity obstruction; it does not prove a
PointPair or solve the simultaneous three-detector supports.

This proof uses the early-eight orientation exactly as the
original necessary reduction, not the stronger sufficient
Gaussian quarter-count recipe. No analytic or Lean assertion
is used. The checker replay is just trial primality, square
residues and literal group arithmetic over F_2399.

    python3 -B check_actual_2399_square_denominator.py | cmp - EXACT-SQUARE-CONTACT-2399.json
    sha256sum -c SHA256SUMS
