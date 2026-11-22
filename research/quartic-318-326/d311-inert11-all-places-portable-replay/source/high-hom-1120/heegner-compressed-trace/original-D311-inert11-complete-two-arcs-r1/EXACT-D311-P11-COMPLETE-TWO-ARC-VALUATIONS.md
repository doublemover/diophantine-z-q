# Two full degree-241 arcs: cancellation of a verified diagonal subtotal

This exact computation takes the same two moving conductor-241 arcs over the same named place at 11 for \(D=-311,\ n=241\cdot311\) as the previous two-path control (c6242b9e). It independently lifts both arcs and evaluates **all 160 factors on each**, not just their one diagonal factor. Each complete signed arc contributes zero to the local valuation. The earlier \(-4\) diagonal subtotal remains correct. This is not the entire valuation at 11, nor a test on the original selected detector.

## 1. Direct exact tame lifting instead of a shell count

Use the canonical short source \(E:y^2=x^3-x+T\) modulo \(11^5\) from the independently replayable horizontal 19-cycle (e82fc6e6). The residue curve, ordered moving eigenvalues \((2,0)\), and all named radicals agree with the earlier path calculation. The two residue generators used for the degree-241 lines are exactly the eigenspaces with eigenvalues 99 and 142 of \(U=4\sqrt{-5}\). The first is independently obtained by projecting \(Vz\) from the second line with \(U+99\); the projection is nonzero because the moving \(V\) has no 241-eigenline. Both named characters are \(-1\), checked by their residue Miller–Gauss evaluations.

Let the extension ring be
\[
 (\mathbb Z/11^5)[z]/(z^{96}+z^4+2).
\]
The residue polynomial is irreducible, so this is an unramified Witt quotient. Units are inverted by residue inversion followed by Newton doubling, with an exact inverse assertion. Lift \(s=\sqrt2\) and the other fixed radicals by their named simple equations. Lift the three torsion generators on the moving source using the following exact affine conditions in the indicated residue discs.

For odd \(\ell\in\{3,241\}\), let \(k=(\ell-1)/2\). Vary \(x\) in the source torsion residue disc, with \(y\) lifted on the chosen sign of the curve. Then solve
\[
 x([k+1]P)-x([k]P)=0.
\]
At the exact solution the two points have opposite signs, as already true in reduction with nonzero \(y\). The unit derivative is \(-\ell\,y([k]P)/y(P)\) in the residue, using compatibility of the invariant differential with \([\ell]\). All affine group denominators in the separate short multiplication chains are units: the intermediate positive scalar ranges are bounded by \(k+1\), never reaching an unwanted inverse pair. For the 16-line solve \(y([8]P)=0\). Its derivative at the residue disc is \(8(3x([8]P)^2-1)/(2y(P))\), a unit by good reduction and the simple 2-kernel root. The two conditions identify the unique prime-to-11 torsion lifts in their residue discs; the replay checks both their equations and exact original reductions.

Quotient by each lifted cyclic 241 subgroup and transport the lifted ordered 16- and 3-lines. Vélu on the \(x\)-coordinates uses the 120 \( \pm \) kernel pairs; the corresponding \(y\)-map is \(y\) times the derivative of the normalized \(x\)-map. The quotient parameters are checked with both degree-two \(t_8\) views, then the 3-quotient \(t_{16}\) is checked similarly. If \(a_0=t^2/(t+2)\) and \(a_1=t(t+4)\), the checked recovery is \(t=(a_1-2a_0)/(a_0+4)\). To recover \(X,Y\), put \(t=t_{16},v=t_{16}^{(3)},b=(v+2)X+1\), and solve \((t+2-X)b-3X=0\) in the genuine flag disc. Both branches used here have a unit derivative. The recovered \(Y=2b-X^4-1\) satisfies the exact curve equation and **both** quotient parameters. The program checks that each coordinate lies in the two-dimensional subring in basis \(1,s\).

## 2. Factor-complete evaluation and exact cancellation

For the two eigenvalues, the four coordinates below are computed modulo \(11^5\) in basis \(1,s\):
\[
\begin{array}{c|cc}
\text{eigenvalue}&X&Y\\ \hline
99 &(39311,2771)&(112926,125334)\\
142&(105619,112639)&(40315,21131)
\end{array}
\]
Both are distinct lifts of the same ordered reduced flag \(Q=(296,149)\), not two names for the same lift. Their exact distances to the fixed calibrated \(Q\) each have valuation one; the diagonal factor of multiplicity two has exact valuation two as before.

Using the exact radical calibration data, evaluate the literal eight signed real packets with all four Atkin factors on each lifted flag. There are 40 indexed seed occurrences and therefore 160 scalar factors on each flag. All valuations are smaller than the precision five, so every entry in the attached table is exact. On both flags the largest valuation is two. The table reproduces the two diagonal contributions of \(-2\) each. Other \(G_5,H_7\) and Atkin factors **cancel them** in the complete product: \(v_{11}(\mathcal U)=0\) on each of the two flags, so each signed contribution is zero.

This is a genuinely factor-complete calculation on these two terms, not a complete local prime calculation. The other terms of the conductor-241 family and the full valuation at the named prime are uncomputed by this packet. The exact signed diagonal subtotal and the vanishing of the two full contributions are compatible.

Replay with Python 3 and python-flint 0.9.0 from the preserved donor-relative layout:

~~~sh
sha256sum -c SHA256SUMS
python3 -B check_D311_p11_complete_arcs.py | cmp - EXACT-P11-COMPLETE-ARCS.json
~~~
