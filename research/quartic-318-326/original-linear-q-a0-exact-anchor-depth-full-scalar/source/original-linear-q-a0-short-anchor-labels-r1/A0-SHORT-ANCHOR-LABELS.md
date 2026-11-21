# A compact original input-0 label tuple with the same scalar and a physical anchor

Use the exact input \(a=0\), the actual signed source chart and fixed polynomial scale \(S=3^{65536}\). For the pinned old 864-bit positive integer \(J\), put
\[
s=1+6^{15}3^{65536}J,\qquad (n_0,n_1,n_2,n_3)=(3723,s,3723,3723).
\]
Keep the exact positive \(h\) from the archived order-only denominator-prime calculation at \(q=3162001\), without changing the scalar progression. The largest label needs only 104775 bits. These are **stored indices**, not stored elliptic coordinates or primes.

The tuple preserves the literal scalar pole at this \(h\), has an actual rational row-287 anchor (existence, not materialized coordinates), and retains the original three-detector denominator-depth cell at this single \(q\). It is not a full Gaussian key, does not assert global detector readiness on these three poles, and supplies no rational PointPair.

## Exact source separation

The generic source theorem **PreparedIntegerSource318.complete_at_index** requires nonzero labels, \(n_1\ne1\), and the literal guards. It requires neither a Lucas equation for \((n_2,n_3)\) nor pairwise distinct labels. Its passage of the later detector points into the completed source still requires the four exact point pairs and the physical anchor. The four mod-5 guard witnesses become \((4,1,4,4)\) from the old certified labels 0 and 1: each guard is a function of just that label and \([h]P\). The signed roots still come from the original chart with the new labels, not from the old Lucas tuple. The scalar real-margin bound is unchanged because its norm is a function of \(h\) alone.

The scalar pole itself is unchanged, not just its real bound or local squareclass. The exact detector prefix slots \(w_0,w_{33},w_{37}\) are
\[
0,\quad\Re(\operatorname{chartU}(h)^2),\quad N(\operatorname{chartU}(h))
\]
by **DetectorGateWitness318.witness_input** and **ScalarActualInputs318.detector33, detector37**. In ScalarForwardWitness318, the four definitions \(N,Q,W,\mathrm{poleInput}\) depend only on these slots and \(n_1\). Thus both tuples give exactly the same **PreparedIntegerSource318.scalarB 0 labels h**, and every already proved property of that scalar at the same \(h\) carries over. No inference about its global PointPair is used here.

## The literal row-287 equation has a new rational anchor

Write \(z_n=-1/U(nR)\) in the original source and now \(Z=z_{3723}^3z_s\). This is a new exact \(Z\); its norm is not imported from the old tuple. All four labels are odd and \(v_3(s-1)\ge65551\). The generic **ActualAnchorRatio318.local_depths**, which does not require the Lucas relation, gives \(r\ne0,\ v_2(r)=0,\ v_3(r)\ge0\) for
\[
r=4096NZ+\operatorname{inverseNorm}(s)/S.
\]
The anchor uses the actual equation
\[
x^2+6y^2-2z^2=3(4096 S NZ+\operatorname{inverseNorm}(s))^2-2S^2.
\]
Divide the coordinates by \(S\). The normalized right side \(c=3r^2-2\) is a square at 2 and 3 by the pinned **AnchorLocalSquareProduction318** generic theorems. At every odd \(p\ge5\), the ternary form \(x^2+6y^2-2z^2\) is isotropic and universal over \(\mathbb Q_p\) (**PadicAnchorUniversality318.represents**), and is also universal over \(\mathbb R\). Consequently \(x^2+6y^2-2z^2-cw^2\) is everywhere locally isotropic. [Hasse–Minkowski](https://doi.org/10.1515/crll.1923.152.129) gives a nonzero rational isotropic vector. Its \(w\) cannot vanish: the ternary is anisotropic at 3 because the nonzero unramified norm \(x^2-2z^2\) has even valuation and a nonzero \(6y^2\) has odd valuation. Divide by \(w\), then multiply all three coordinates by \(S\). This produces precisely the physical **ScalarCompleteSource318.Anchor S (NZ) (inverseNorm s)**, not an anchor for a changed scale. No specific rational coordinates were evaluated and this appeal to Hasse–Minkowski is classical.

## Finite replay at the original \(q\)

The actual half-generator is \(R=(1+\sqrt2,2\sqrt2)\) on \(y^2=x^3-(3-\sqrt2)^2x\). Retaining \(R,h\) keeps the two archived depth-one formal parameters at \(q\) unchanged. On either nonformal arm, with the original sign convention, the only new nonfirst label Padé denominator is \(Q_J=1+5(V(3723R)-1)/13\). Exact independent affine reductions give \(1596550\) and \(2797455\), both nonzero. The other retained Padé rows, the charts of \(R,sR\), and the formal depths at the two places are unchanged. The new products \(Z\) are \(761073,2630470\bmod q\), giving
\[
(c_0,c_1,c_2)\equiv(1,3143945,3029174)\pmod q,\qquad
c_1=\Re Z+NZ,\quad c_2=NZ .
\]
All three squares are nonzero and distinct modulo \(q\), hence distinct as rational numbers. For any \(t\) of depth \(-1\) at \(q\), the previous literal pole expansion applies to this tuple too: the fold weight valuations are \(3,3,3\), and \(v_q(b_{190})=v_q(b_{241})=v_q(b_{292})=1\). At \(qt\equiv1\bmod q\), the units \(b_j/q\bmod q\) are \((2371501,2509447,2023566)\). The unchanged formal parameters and real margin are certified by the [exact original order-only calculation](https://github.com/doublemover/diophantine-z-q/tree/f767adfb/research/quartic-318-326/actual-linear-q-local-numerical-check/linear-q-literal-order-only-canary-r2); this replay independently recalculates the affected affine charts, not those old inputs. This does not certify the full Gaussian wheel at that prime or any contact prime.

The three five-contact rows remain distinct except for their common zero root: within a fixed nonzero root the squared scales are distinct, and across roots the four nonzero roots have different rational squareclasses \(-2,-1,2399,-814\), unchanged by squares of scales. Repeating labels does not collapse the three affine slope rows.

## What the shorter tuple does and does not save

Let \(D\) denote just an integral algebraic clearing for all slopes, before the further common enlargement \(Q\) of the linear-\(q\) construction. If \(A_j\) is the absolute reduced numerator of \(c_j\), \(j=1,2\), take \(D=2\cdot407\cdot2399\,A_1A_2\). This makes \(D/c_j\) integral and its divisibility clears all four nonzero contact root denominators. For \(h_2\) the base-2 absolute logarithmic height,
\[
h_2(\Re Z)\le2h_2(Z)+2,\quad h_2(NZ)\le2h_2(Z),\quad
h_2(c_1)+h_2(c_2)\le6h_2(Z)+3.
\]
In the earlier [explicit height comparison](../original-linear-q-a0-archived-clearing-height-floor-r1/ARCHIVED-A0-COMMON-CLEARING-HEIGHT-FLOOR.md), \(P=2R\) has \(x(P)=(57-28\sqrt2)/8\), primitive minimal polynomial \(64T^2-912T+1681\), both roots greater than 1. Therefore \(h_2(x(P))<11/2\), and the same error bound gives \(\widehat h_2(P)<8\) in that notation. As \(\lvert h_2(z_m)-m^2\widehat h_2(P)\rvert\le5\), our tuple gives \(h_2(Z)\le8(s^2+3\cdot3723^2)+20<9s^2\). Hence
\[
\log_2 D<55s^2<2^{209556}.
\]
This finite upper bound for the literal slope-clearing alone replaces the doubly exponential archive growth. It does **not** bound the later \(Q\), the Gaussian sift parameter, or the actual simultaneous-prime key. It is still far beyond feasible coefficient materialization. Indeed the exact general final-anchor floor forces the chosen slot-190 \(-1\) prime to need more than \(2^{103860}\) bits even for replacement anchored labels in this framework. The useful distinction is that the shorter labels and their local elliptic certificates can be handled before expansion. No algorithm lower bound is claimed.

## Exact pins and replay

Unchanged native source files from the original retained r22 replay:

- PreparedIntegerSource318.lean e3ecec834054e138eb6cc64c92f0e431510c64a878803d689fa55a9fdf06c423 (generic exact consumer).
- ScalarActualInputs318.lean 669eb03d31c5490f7278608a416e1e44ec64d10aa90c044c64c6636759e810f1 and ScalarForwardWitness318.lean 9b21f269bbf73da643a7259f71dc67ea835a52aaa97bbb6d449549004bf7038c (identity of scalar).
- ActualAnchorRatio318.lean 2f248c0f28f5a8349040950d3c22d1c756b7747ff90664fbb129484432bcc490, AnchorLocalSquareProduction318.lean 2463e247e93733182ba7a0fe9ef5510c26c55fc9c4081ecefc9bad1dfd8bea34, PadicAnchorUniversality318.lean 4a6d9427bf7f31cb95038a407d7bd4dce76ade943de4e632627cd5b29da3c4ef, ScalarCompleteSource318.lean a0f74e00bdd0be89dee1cac08d935908bb225610dba88d9564d9c99916a03323 (actual anchor).

~~~sh
python3 -B verify_short_anchor_labels.py | cmp - EXACT-A0-SHORT-ANCHOR-LABELS.json
sha256sum -c SHA256SUMS
~~~
