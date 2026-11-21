# The same numerical marked candidate meets the three small-place pole tests locally

This extends the repaired exact \(p=17\) result for
\(D=143606921256815429642705807535961\), same \(J\), same exact
accepted \(h\), same historic \(p_a\) cell and all older contacts.
Both multipliers \(a,b\) are local square units at \(2,3,17\).
The three local choices below belong to the same marked cover and
each opens to a valuation annulus of genuine original pole values.
This is not rational simultaneous localization or a PointPair.

## Actual lower bounds on the same 16 coefficients

Write \(U_h,V_h\) for the genuine reciprocal chart, respectively
the coordinate \(2y/(x^2+D_0)\) and its original quartic ordinate,
on \(E_{D_0}\) with \(D_0=(3-\sqrt2)^2\).
Keep the actual constants \(k=-1+7\sqrt2/4,\ m=39/8-9\sqrt2/2\),
shift \(S=(kV_h/U_h-m)/(k^2+D_0 U_h^2)\),
\(G=U_h^2S^2\), and \(B_0=k^2+mS+D_0G\).
Use the literal \(P_G,Q_G,P_J,Q_J\) and source formulas for both
kinds of ratio, not an arbitrary integrality assumption.

At \(2\) the normalization is \(v_2(2)=1\) on the ramified quadratic
field. From \(U_R=2y_R/(x_R^2+D_0)\), the numerator is \(4\sqrt2\) of
depth \(5/2\) and denominator is \(14-4\sqrt2\) of depth 1.
By \(x([2]R)=U_R^{-2}\), the formal parameter of \([2]R\) has
depth \(3/2\). Odd multipliers preserve that depth; doubling adds
one whenever the depth exceeds 1 because its linear term is
\(2z\), higher terms having depth at least \(2v(z)>v(z)+1\).
Consequently for odd positive \(n\) we have \(v(U(nR))=3/2\),
and \(v(U_h)=3/2+v_2(h)>3/2\) for the concrete even \(h\).
All four literal labels are odd by the \(\bmod2\) Lucas period,
also checked by computer. The two-scale reciprocal product has
depth \(-6\), conjugate of equal depth, norm of depth \(-12\)
and half-trace of depth at least \(-7\). Thus the actual
\((c_0,c_1,c_2)\) have depths \((0,-12,-12)\).

Let \(d_h=v(U_h)>3/2\). The true \(V_h\) is a unit by
\(V_h^2=1-D_0 U_h^4\). Since \(v(k)=-3/2,\ v(m)=-3\), the
compression has depths
\[
 v(S)=3/2-d_h,\quad v(G)=3,\quad v(B_0)=-3/2-d_h .
\]
The last equality uses the unique lowest \(mS\)-term. The Padé
argument has depth 6, so both \(P_G,Q_G\) are units and the
commonLog has depth \(3/2\).
Primary \([nh]\)-ratios are integral by the exact \(A=kV_h/U_h\)
identity. On the opposite \([n(h-1)]\) arm the multiple is odd:
its \(U\) has depth \(3/2\) and its \(V\) is a unit. The alternate
Padé denominator is a unit (reduce \(V\) modulo \(\sqrt2\) to 1),
and the alternate numerator is integral. Hence all eight ratios
are integral. In this ramified field, an integral \(\alpha+\beta\sqrt2\)
has both rational components integral because the two valuation
classes are integer and half-integer and cannot cancel.
The only apparent half in the unweighted leaf formulas, besides
the cancelled half-scaled \(U^2\) entry, is \(w_{124}\), allowed
depth \(-1\). Its square occurs with factor 8 in \(w_{137}\), and
both linear appearances in the last imaginary component
have factor 4. Thus the last full leaf remains integral. Leaf 15
is the same denominator-cleared quadratic expression as in the
17-adic certificate. Every one of the sixteen leaf pairs is
2-integral on this exact source.

At \(3\) the quadratic field is unramified, with residue \(\mathbf F_9\).
The same lifted actual \(R\) mod 9 has order 4 mod 3 and
formal parameter \((6,3)\) at its first return. The original
\(h\) is divisible by \(4\cdot3^4\), hence \(v(U_h)\ge5\).
The true alternate charts satisfy \(V_{[n(h-1)]}\equiv
V_{[-n]}\bmod9\). Their unit denominators and the four Laurent
reciprocal factors are replayed directly; they give
\(c_0,c_1,c_2=(1,6,4)\bmod9\), exactly depths \((0,1,0)\).
Here \(k,D_0\) are units and \(v(m)=1\). Setting \(d_h=v(U_h)\)
gives \(v(S)=-d_h\), \(G\equiv k^{-2}\bmod3\),
\(v(B_0)=1-d_h\), and \(D_0G^2\equiv1\bmod3\).
The unique \(16x^2/195\) term of \(P_G\) has depth \(-1\)
and the other terms are integral. Also \(Q_G\) is integral
and nonzero by the actual denominator lemma. Thus
\[
 v({\rm commonLog})=-2-v(Q_G)\le -2 .
\]
The exact \(Q_J\) denominators are units, \(P_J\) has depth
at least \(-1\), and the first alternate polynomial has
integral denominator 5. All eight actual ratios are integral,
using again the true \(A\)-identity for the primary charts.
In the unramified basis \(1,\sqrt2\), integral elements have
both rational coordinates 3-integral. The leaf pair formulas
are consequently all integral at 3, with the same leaf 15
cancellation. At 17 use the previously sealed exact
integral-leaf argument with the same \(h\).

## Exact three original pole depths

Choose local \(W=c_1w\) of valuations \(-600,-6,-1\) at
\(2,3,17\) respectively. These are valid projected local
points because \(W^2-s,W^2-t\) are squares times the same
positive unit phase and \(a,b\) are square units.
Write \(v(w)=-d\) and \(v(c_j)=e\). In each slot
\(v(T_j)=2(e-d)<0\), and the actual identity
\[
 F(T_j)=T_j^5\prod_{r\ne0}(1-r/T_j)
\]
shows it is a nonzero square: the four units are \(1\bmod8\)
at 2 and \(1\bmod p\) at 3,17. The actual \(\Delta_j\) is
nonzero of depth \(2(e-d)\), and the three literal weights
at this slot have depths \(6d+4e,\ 6d+64e,\ 6d+244e\).
By the above coefficient bound these weighted depths are
all positive, at least 3 at 2. The true square-plus-leaf
fold stays at 1 within the integral pair algebra, so
\(2\tau_j\) is a unit (no use of an étale quadratic
basis at 2). The detector formula gives the exact pole
depth \(2d-12e-2v_p(2)\). The three arrays are:
\[
\begin{array}{c|ccc}
 p & 190 & 241 & 292\\ \hline
 2 & 1174 & 1318 & 1318\\
 3 & 14 & 2 & 14\\
17 & 2 & 2 & 2
\end{array}
\]
All three pole values are actual nonzero local squares, and
these depths exceed the literal required \(3,1,2\).
The same proof applies to deeper \(W\) at 2 or 3, with linear
adjustment of the depths, and to other even h with the same
small period \(20\mid h\), \(v_3(h)\ge4\), \(v_{17}(h)\ge1\)
(including larger \(v_{17}(h)\)).

This closes the three exact small-place trace conditions
on local points of the repaired auxiliary cover. It does
not give a single rational \(W\), actual other root support,
saturation compatibility, or any final quartic witness.
