# Exact sixteen-leaf threshold for a nonnegative odd contact pole

Keep the same original detector slot, guarded h, actual coprime
Lucas labels, and nonzero b. At p not in {2,3,7,17} require
c,Delta p-units and positive odd e=v_p(F(c²t)). This is a paper
iff for v_p(b)>=0 at this one contact, not an iff for PointPair.

By the early-eight theorem 63be7c0a, if there is no admissible
split orientation, v_p(b)<0 with odd parity. Otherwise the
orientation is unique: on the primary arm [2h]R reduces to O
and on the opposite arm [h−1]R reduces to O or T0=(0,0).
The opposite arm fails the eight early tests, hence its final
fold valuation is <=−64e. This includes p=41 whenever the usual
unit c,Delta hypotheses hold; no norm sign at 41 is used here.

## Exact local iff

On the primary arm denote by L_k the literal weighted leaf at
position k=1,...,16, including the first scalar w37² w156, and
let lambda_k=v(L_k), allowing infinity for a zero leaf.
All finite lambda_k are odd. The literal chain starts at 1 and
each step has the form X_k=X_(k−1)²+L_k. Exact coefficient
parity forbids cancellation with the previous square. Hence

    v(X_k)=min(2 v(X_(k−1)),lambda_k),
    m := v(X_16)=min(0,min_(1<=k<=16) 2^(16−k) lambda_k).

All these running valuations are finite and nonpositive. Write
mbar for the final opposite valuation. With mbar<=−64e and
nonzero b, we have the exact equivalence

    v_p(b)>=0
      iff m>=−floor(e/2)
      iff lambda_k >= −floor(e/2^(17−k)) for every k.      (T)

If m>=−floor(e/2), then −m<−mbar. The primary term strictly
dominates in the inverse trace X_16^(-1)+Xbar_16^(-1):
its valuation is exactly −m. Thus the trace quotient has valuation
m and the actual pole valuation is e+2m, a positive odd integer.
If instead m<−floor(e/2), both reciprocal valuations exceed e/2.
Their sum has valuation >e/2 or is zero. The zero case would make
b=0 by literal total division; otherwise v_p(b)<0, still odd.
This proves the iff, regardless of possible cancellation when
both places fail.

For e=1, condition (T) says exactly that **all sixteen weighted
leaves are positive or zero on the one primary arm**. In this case
the chain is 1 mod p there, while the opposite inverse vanishes
mod p. Thus the trace quotient is 1 mod p and v_p(b)=1. This is
the exact local valuation of the original pole, not merely a norm
depth lower bound. For any allowed e where (T) holds, the same
pole has no local obstruction from a negative odd exponent. The
full finite-support replay can therefore use checked higher odd
e and (T), instead of requiring all odd contacts to be simple.
It still needs all odd support and the same actual h, not merely
compatible h at each prime separately.

## An opposite-depth restriction without inspecting late leaves

Let d_minus be the depth of the actual chart U([h−1]R) on the
opposite arm. This is positive and finite on the guarded original
h, since h≠1 and the source R is nontorsion. For any p-unital
integer n, the depth of U([n(h−1)]R) is also d_minus.
Indeed, use the exact identity U(T0+P)=U(P) on this curve.
For affine ordinary coordinates the translation is
x'=-D_c/x, y'=D_c y/x², which gives this identity directly;
O and T0 have U=0 as well. Subtract an actual T0 if necessary
to enter the formal disk. There U has initial term −2z with unit
coefficient, and multiplication by a p-unit preserves its depth.
The norm-free chart equation and V+1 unit then give

    v(V([n(h−1)]R)−1)=4 d_minus.

The original n_2,n_3 are coprime, so at least one is a p-unit.
The corresponding conjugated early leaf is position 9 or 10
on the primary arm and has weighted valuation 4 d_minus − e.
Condition (T) therefore requires

    4 d_minus >= e − floor(e/128).                         (D)

This is necessary for the actual PointPair and for v_p(b)>=0,
without evaluating any late Padé coefficient. For ordinary opposite
depth d_minus=1 it excludes every odd e>=5 (the right hand
side is monotone and at e=5 is 5). It does not decide e=3 or
exclude higher depth on the fixed generator. This restriction is
independent of the exact first-leaf norm-depth cut.

## Scope

All equations refer to the original sixteen ordered coefficients
and unchanged stored pole. Sources and guard/odd-denominator proof
are pinned in 63be7c0a and 8a0f698e. This refinement uses no prime
scan and constructs no complete h,t or rational PointPair.
