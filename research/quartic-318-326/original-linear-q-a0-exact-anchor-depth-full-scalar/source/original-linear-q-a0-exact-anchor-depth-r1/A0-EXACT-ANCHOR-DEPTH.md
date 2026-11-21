# An original input-0 scalar and anchor at the sharp translated 3-adic depth

In the original source chart, retain the same positive \(h\) as the [archived \(q=3162001\) order-only check](https://github.com/doublemover/diophantine-z-q/tree/f767adfb/research/quartic-318-326/actual-linear-q-local-numerical-check/linear-q-literal-order-only-canary-r2), but take new labels
\[
 s_\star=1+2^{21}3^{32767}\,5\,17^2,\qquad (n_0,n_1,n_2,n_3)=(3723,s_\star,3723,3723).
\]
The scalar label is odd, nonzero, not 1, and exactly 51966 bits as an integer index. This version does **not** keep the old scalar value or its earlier scalar-support residues. It constructs the real range and original **SmallPrepared** valuations/squares on the new actual scalar at the same \(h\), the physical anchor by Hasse–Minkowski, and the three new literal detector local cells at this one \(q\). It does not deliver four Ready poles, the full Gaussian wheel, the contact primes, or any PointPair.

## 1. The original scalar local conditions at the same actual \(h\)

Write \(H=w_{37}=N(U(hR))\), \(W=w_{33}\)- and \(H\)-dependent packed scalar in ScalarForwardWitness318, and \(I=\operatorname{inverseNorm}(s_\star)\). The exact scalar translation is \(I=N(U((s_\star-1)R))\) by **ScalarTranslatedIndex318.scalar_inverse_norm**. The replay verifies
\[
\begin{array}{c|ccc}
 &v_2&v_3&v_{17}\\ \hline
 h&6&5&1\\
 s_\star-1&21&32767&2
\end{array}
\]
and \(20\mid h,\ 20\mid(s_\star-1)\). Consequently **ScalarTwoThreePreparation318.unit_two** applies with equality \(6+15=21\); **unit_three** applies since \(h,s_\star-1\) are even and \(5<32767\). Thus \(W\) is a unit at 2 and 3. These are the direct integer-index unit lemmas, not an invocation that the retuned label remains in the old numeric scalar progression.

At 17 the two square roots of 2 modulo \(17^2\) are \(244,45\). Exact affine calculation in \(\mathbb Q(\sqrt2)\) gives the chart values \(U([20]R)\equiv34,272\bmod17^2\) on these arms. Both are on the formal disk: equivalently one first checks that \([20]R\) reduces to the identity at each arm (the two orders are 10 and 4). On this disk \(U=2y/(x^2+D_E)=-2z+O(z^5)\) for the usual parameter \(z=-x/y\), with unit leading term. The leading formal depth at 17 is therefore exactly one, and the formal logarithm preserves the depth at odd good primes on \(17\mathbb Z_{17}\). Multiplying this actual point by an integer \(k\ne0\) makes its depth \(1+v_{17}(k)\). With \(k=h/20,(s_\star-1)/20\), the two split arms give \(v_{17}(H)=4,\ v_{17}(I)=6\). The literal half-trace of \(U(hR)^2\) has depth at least 4. The original \(R_{\rm scalar}=\mathrm{inputR}(0)\) is a 17-adic unit, so
\[
N_{\rm pack}=1+(H/R_{\rm scalar})^2+2w_{33}/R_{\rm scalar}\equiv1\bmod17,
\qquad Q_{\rm pack}=I/(H R_{\rm scalar}^{15})\equiv0\bmod17 .
\]
Thus \(W=N_{\rm pack}^2+R_{\rm scalar}Q_{\rm pack}^2\equiv1\bmod17\). The same exact thresholds/square theorems as in ScalarSmallPrimeProgression318 now give the literal actual scalar \(b\) of depths \(4,2,2\) at \(2,3,17\), a square at each. Since \(H\) only depends on \(h\), the certified strict real margin is unchanged; **PreparedIntegerSource318.scalar_domain** gives \(0<b<17\) for the new label.

## 2. The exact anchor and unchanged guard method

The original row-287 scale is still \(S=3^{65536}\). The normalized anchor ratio is \(r=4096NZ+I/S\), with the newly calculated \(Z=z_{3723}^3z_{s_\star}\), not the old norm. All labels are odd. As \(2+2v_3(s_\star-1)=65536\), ActualAnchorRatio318.local_depths gives \(v_2(r)=0,\ v_3(r)\ge0,\ r\ne0\). Reapply the exact generic anchor argument in the [short-label donor](../original-linear-q-a0-short-anchor-labels-r1/A0-SHORT-ANCHOR-LABELS.md): \(3r^2-2\) is a square at 2 and 3; the ternary is locally universal elsewhere and anisotropic over \(\mathbb Q_3\); a [Hasse–Minkowski](https://doi.org/10.1515/crll.1923.152.129) point on the homogenization has nonzero homogenizing coordinate. Scaling the resulting affine triple by \(S\) yields the exact rational physical anchor for these new labels. Its coordinates are not computed. The previous general floor requires \(v_3(s-1)\ge32767\) on any anchored original tuple, so this attains the sharp required **depth**, not an asserted minimum over all viable integer labels or keys.

At 5, \(R\) has order 5 (independent affine check of \([4]R=-R\) in the replay). The new scalar index and the old one are 1 modulo 5, so the old nonzero mod-5 scalar guard is valid with the same \(h\); repeated \(3723\) uses the same original guard. Thus the guard residues are \((4,1,4,4)\).

## 3. The new order-only \(q\) cell and numerical stop

Both original \(q\)-adic formal-depth-one rows depend on \(R,h\) alone and are unchanged. The replay checks the new nonformal affine charts modulo \(3162001\). In the arms \(772448,2389553\) the two new scalar-label Padé \(Q_J\) values are \(3035038,2764656\); the repeated \(3723\) values are \(1596550,2797455\). The base Padé denominators remain the same. The new scale residues are \((1,1298587,1842649)\) with distinct nonzero squares. The old exact trace expansion gives depth one in all three poles and
\[
(b_j/q)\bmod q=(2371501,1354357,739351)
\qquad(qt\equiv1\bmod q).
\]
This is genuinely the original chart on a new label tuple, not the old \(q\) calculation reused with the new label tacitly left fixed. Only this one place is evaluated for all three detector poles.

By the same height comparison and algebraic clearing argument in the short-label donor, the slopes admit a positive integral clearing \(D\) with \(\log_2D<55s_\star^2<2^{103938}\). This does not bound enlargement \(Q\) or any prime value from above. The general final-anchor floor still gives a mandatory contact prime length greater than \(2^{103860}\) bits, even at this least translated 3-depth. Do not expand the primes. Treat this as a small exact source specification available for symbolic work and finite reductions, not a materialized simultaneous-prime roster.

## Replay and pins

The exact inherited author source is bound in the short-label donor. Additional frozen native names: ScalarTranslatedIndex318.scalar_inverse_norm, ScalarTwoThreePreparation318.unit_two/unit_three, ScalarSmallPrimePreparation318.actual_pole_thresholds, ScalarLocalSquares318.actual_pole_squares. The finite checks use Python standard library only and do not run Lean.

~~~sh
python3 -B verify_exact_anchor_depth.py | cmp - EXACT-A0-ANCHOR-DEPTH.json
sha256sum -c SHA256SUMS
~~~
