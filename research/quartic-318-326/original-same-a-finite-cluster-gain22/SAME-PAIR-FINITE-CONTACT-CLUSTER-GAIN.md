# A +22 directional height bound from finite divisibility of the same pair

This sharpens the finite part of the published same-A direction for both literal 318/326 tables. It retains the selected \(t=32u/v\), the literal arithmetic maximal curve, the actual fine models and the very same two Hodge tensors. The previously used +64 theorem and its constants are unchanged and remain sufficient. This note changes no native source constant.

Let \(b=(0,32,76832,-343)\) be the four exact finite contacts, \(D_0=2765952000\), and \(Q=(dt)^2/\prod_i(t-b_i)\). The old differential pair is \((S_0,S_1)=D_0^2(32Q,tQ)\). We prove that on both original proper fine models its two sections lie in
\[
 C\,D^{\otimes 2},\qquad
 C=4D_0^2/(3\cdot5^2\cdot7^3)=1189580636160000
\]
for \(D\) the original relative dualizing line. At infinity the pair is still exactly the one previously bounded by \(420\cdot512\,D_0^2\) in squared-Hodge norm. Finite division therefore improves the bound on the height of its unchanged ratio.

## 1. Exact four-contact clustering on the original vertical DVR

Take a height-one stalk on the original regular semistable fine model, above rational \(p\). Its special fibre is reduced, so the stalk is a DVR in which \(p\) is a uniformizer. Work on that original stalk, not on the ramified selected height-trait curve. The fundamental differential has coefficients in the DVR in a local frame of \(D\). Its relative derivation kills \(p\), so \(v(df)\ge v(f)\) for every nonzero rational \(f\), by writing \(f=p^{v(f)}u\) with \(u\) a unit. We write \(v\) also for the coefficient valuation in the indicated frame and allow \(+\infty\) for zero.

With sorted depths \(a\le b'\le d'\le h\) of the four \(t-b_i\), differentiation of a term of depth \(h\) gives
\[
                  v(Q)\ \ge\ h-d'-a-b'\ \ge\ -a-b'.
\]
If \(v(t)<0\) then all four depths equal \(v(t)\); the sharper direct expressions \(v(Q)\ge-2v(t)\) and \(v(tQ)\ge-v(t)\) give integrality. For \(v(t)\ge0\) the exact table is:

| Rational prime | Nontrivial residue cluster | Smallest depth of a gap in that cluster |
| --- | --- | ---: |
| 2 | \(0,32,76832\) | 5 |
| 3 | \(32,76832,-343\) | 1 |
| 5 | \(32,76832,-343\) | 2 |
| 7 | \(0,76832,-343\) | 3 |

All other \(p\) have four distinct residues because the six gap factors are supported on \(2,3,5,7\). The table is valid over any residue extension: if \(t\) reduces into the triple there is one unit difference (the fourth root), and at least one of its three cluster depths is at most the least gap depth by the ultrametric inequality. If it does not, at most one depth is positive. Thus \(a=0\) and \(b'\) is bounded by the last column, without an assumption about the reduction of the chosen height point.

At \(p=2\) the first component \(32Q\) is integral by the bound \(-5\). For the second: if \(t\) is a unit there is at most one positive root depth and \(tQ\) is integral. If \(0<v(t)<5\), the three even-root depths all equal \(v(t)\), and the odd-root depth is zero. In this case \(v(Q)\ge -v(t)\). If \(v(t)\ge5\), use \(v(Q)\ge-5\). Therefore \(tQ\) is also integral at 2. So even without the arithmetic square-root equations the pair \((3\cdot5^2\cdot7^3)(32Q,tQ)\) is integral and the signed gain below would give +23.

## 2. An extra factor of four from the actual arithmetic cover

On the actual characteristic-zero function field of each fine component, pulled back from the genuine maximal curve, the exact square-root equations are
\[
 z_i^2=c_i(t-b_i),\qquad (c_0,c_1,c_2,c_3)=(-14,-6,42,-21).
\]
This uses the checked arithmetic four-root function field, not its naïve integral normalization as a model. In the original vertical DVR, \(d c_i=0\); hence
\[
 v(dt)=v(2z_i\,dz_i/c_i)\ \ge\ v(2)+2v(z_i)-v(c_i)
                                     = v(2)+v(t-b_i).
\]
The inequality for the rational function \(z_i\) is the same DVR derivative argument, and works whether or not \(z_i\) is integral. This improves the previous bounds for \(v(Q)\) by \(2v(2)\), with the same two components. At every vertical above 2 both components are thus divisible by \(2^2\). No prime-to-2 division or unramified comparison of integral four-root **charts** is invoked; only the exact generic functions are pulled to the fine curve.

Let \(E=3\cdot5^2\cdot7^3=25725\). It follows that \((E/4)(32Q,tQ)\) is integral vertically, including the loss at 3,5,7, and remains integral horizontally: 4 is a unit there and the same index-two branch argument used for the old sections applies. In particular at infinity \(Q\) has order 2 and \(tQ\) order zero. Normality and invertibility of \(D^{\otimes2}\) extend these sections from height one. Since \(C=4D_0^2/E\) is an integer, the two original sections are divisible by this exact common scalar on both original proper full-frame atlases.

## 3. Exact gain on the original height comparison

After the actual proper trait pullback, use the same integral isomorphism \(\Theta=\Psi/210\) on the same Hodge bundle. Thus \(x_i=\Psi_L^{-1}(210S_i)\) of the old proof are both in \(C H_w^{\otimes2}\), where \(H_w\) is the primitive Néron Hodge determinant lattice. In a single rational frame of \(H^{\otimes2}\), the finite local maximum multiplied by its frame norm is bounded by \(|C|_w\). This follows even at a singular specialization since the \(C\)-divisibility and line isomorphism were established on the original model before pullback. The generic ratio is still \(x_1/x_0=t/32=s\), with neither component replaced.

At each archimedean embedding the **same old** actual bound is \(420\cdot512\,D_0^2\). Finite local norms in this normalization sum by the product formula to
\[
  \sum_{w\,{\rm finite}}\log|C|_w=-[L:\mathbf Q]\log C .
\]
Thus the same normalized degree argument now proves
\[
h(s)\ \le\ 2h_Y(A)+\log(420\cdot512\,D_0^2/C)
        =2h_Y(A)+\log(1382976000)\ <\ 2h_+(A)+22.
\]
Here \(h_Y=h_+\) is the same metric identification as in the prior reverse, not the separate modular Jacobian height. The strict inequality follows from \(\exp(1)>\sum_{j=0}^6 1/j!=1957/720\) and the exact integer comparison \(1957^{22}>1382976000\cdot720^{22}\). Without the dyadic root step the new argument gives \(5531904000<\exp(23)\). No alteration of the +64 proof or of either original polynomial, winner selection, field bound or strict thresholds is needed. This is a stronger paper estimate on the same pair, not a Lean proof of it.
