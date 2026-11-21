# The surviving numerical marked cover cannot meet the three original 17-adic squares

This concerns instance B of linked-detector-numeric-two-factor-local-cover-r1
(manifest bed7a5afd4651e45b9ecd5415cc839693748e5e6256d0b5cb35a2739406bbda7):
\[
a=415721\cdot 163199081,\quad b=16990081\cdot17238721,\quad
W=c_1w,\quad W^2-s=aU^2,\quad W^2-t=bV^2,
\]
where \(s=-32/407,t=1/2399\). This is a **direct local obstruction**
on the mandatory three original pole squares, stronger than the
optional \(B\)-saturation obstruction at 23. It does not assert
nonexistence of points on the abstract two-factor cover.

The exact same sixteen-index labels over both 17-adic arms
replay the two order periods (10,4) and their literal four
reciprocal values modulo \(17^2\). They give
\[
(c_0,c_1,c_2)=(1,216,84)\bmod17^2,\quad
v_{17}(c_2^2-1)=1,\quad c_1^{-2}=15\bmod17.
\]
This is label data only, independent of \(h\); in particular
reselecting a compatible \(h\) or multiplying a marked point
does not change these coefficients. At \(17\), \(s=15,t=9\)
and both \(a,b\) are nonsquare units. If \(W\) had negative
valuation, \(W^2-s=W^2(1-s/W^2)\) would be square, impossible
with \(a\) nonsquare. If it had positive valuation (or were
zero), the residues \(W^2-s=2,W^2-t=8\) would be squares, also
impossible after division by \(a,b\). Thus \(W\) is a unit.

For \(X=W^2\bmod17\), test both conic factors, allowing a zero
residue until its higher depth is considered. The necessary
finite list is exactly \(X=4,15,9\). The three original
arguments \(T_j=c_j^2w^2\) reduce to \((15X,X,15X)\).
The literal five-factor polynomial is
\(F(T)=T(T+1/2)(T+1)(T-s)(T-t)\), with distinct roots modulo 17.
Its residue at 4 is \(3\), nonsquare. Hence \(X=4\) fails in
the middle slot and \(X=15\) fails in each outer slot.

The case \(X=9\) has both \(T_0,T_2\equiv-1\bmod17\).
Since \(w\) is a unit,
\[
(T_2+1)-(T_0+1)=(c_2^2-1)w^2
\]
has valuation one. Both individual depths are positive, so
at least one is exactly one. The other four factors at
that slot are units, and the full \(F(T_j)\) has odd valuation.
If any other slot has an exact zero, that too is forbidden by
the nonzero pole requirement. This proves that no simultaneous
cover point at 17 has all three original \(F(T_j)\) nonzero squares.
The exact source identity
\(b_j=F(T_j)(\tau_j/(c_j^5(T_j-1)^3))^2\)
on the admitted nonzero chart transfers the obstruction to
its required \(b_j\), regardless of the surviving numerical
ordinary radical and regardless of scalar/trace adjustment in \(h\).

## Minimum sign change on this same-J chart

If \(a\) remains a nonsquare unit at 17 but \(b\) is changed,
then \(b\) **must** become square to avoid the above contradiction.
In the \((-,+)\) case the analogous list is \(X=1,8,9\):
\(X=1\) puts both outer slots at the simple root \(s\bmod17\)
with difference of depth one, so fails; \(X=9\) still fails
by the preceding \(-1\) argument. The only remaining necessary
branch is \(X=8\). This does not supply an actual full
17-adic projector with all trace depths; in that branch
the outer arguments both lie near \(1\).
For the **original full-\(B\) strategy**, which requires
\(a,b\) square units also at 17, a new \(q_a\) is mandatory
if \(p_a,J\) are retained, and a new \(b\)-pair is mandatory
for this instance (its squareclass is also nonsquare at 23).
The all-square phase permits negative \(W\)-depth and
the conventional prepared-small-place route; it is not an
existence proof of a full-\(B\) numerical candidate.

Both exact deductions depend only on the genuine old chart
coefficients and simultaneous conic equations, not on the
October pointwise 2-converse. No proof bypassing the two-factor
cover altogether is ruled out.

Replay:
    python3 check_numeric_p17_obstruction.py | cmp - EXACT-NUMERIC-P17-OBSTRUCTION.json
