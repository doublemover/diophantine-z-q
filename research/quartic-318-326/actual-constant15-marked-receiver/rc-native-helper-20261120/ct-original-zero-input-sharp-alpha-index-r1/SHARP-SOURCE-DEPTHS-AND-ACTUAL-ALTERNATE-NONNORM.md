# Sharp original zero-input index requirements and an admissible alternate scalar that is not a norm

The input remains \(a=0\), and the original folds and final physical scale remain unchanged. This gives sharp local index requirements on a proposed compact Γ branch using the literal cyclic source, and another exact source scalar that meets the scalar guards and has a rational original anchor, but whose literal Γ is not everywhere locally soluble. It neither obstructs the old fixed scalar nor decides whether some other index produces a rational PointPair.

Let \(P_0=(1+\sqrt2,2\sqrt2)\) on \(E:y^2=x(x^2-(3-\sqrt2)^2)\), \(U_j=U([j]P_0)\) with \(U=2y/(x^2+d^2)\), \(d=3-\sqrt2\). The common index is \(h\ne0\); the literal second label is \(n\ne0,1\) and its translated index is \(i=n-1\). Keep
\[
R=4376874610839020,\quad \beta={114444R}/{(17\cdot144)}=204618888056724185,\quad D_0=1+114444R,
\]
\[
 H=\operatorname{Norm}U_h,\quad I=\operatorname{Norm}U_i,\quad
 N_0=\operatorname{Norm}(1+U_h^2/R),\quad Q_0=\frac{I}{HR^{15}},\quad
 W=N_0^2+RQ_0^2,\quad c=\frac{12W}{D_0},\quad b=17\beta c^2 .
\]
These are the literal slot 33/37, translated inverse norm and pole equations. In particular \(N_0=1+(H/R)^2+\operatorname{Tr}(U_h^2)/R\). The Γ receiver uses \(\delta=1-\beta c^2\), not a replacement rational parameter.

## 1. Odd \(R\)-support forces the original formal preparation

For odd \(p\mid\beta\), local solubility of the same Γ is **equivalent** to integrality of \(c\) at \(p\). If integral then \(\delta\equiv1\bmod p\) and choose \(u=2/\sqrt\delta,\ A=0,\ B=1/\sqrt\delta\) in Γ. If \(c\) has a pole, \(\delta\) has odd valuation \(1+2v_p(c)\). Replace it by a square-equivalent value of valuation 1, scaling the affine variables accordingly. The projective infinity would require both \(5B^2=u^2\) and \(5A^2=\beta u^2\), impossible. In the affine chart for \(p\ne5\), if \(v_p(u)\ge0\) the equation \(5B^2=u^2+1/\delta\) has odd right-hand order \(-1\). If \(v_p(u)<0\), multiplying the even-order leading \(u^2\) by \(\beta/5\) in \(A^2=(\beta/5)(u^2-4/\delta)\) gives odd order. At \(p=5\) the \(B\)-equation rules out \(v_p(u)<0\) and the \(A\)-equation rules out the other case.

At every odd \(p\mid R\), \(v_p(R)=1\) and \(D_0,12\) are units. The two terms in \(W\) have even and odd valuations, so cannot cancel. Integrality of \(c\) means **both** \(N_0,Q_0\) integral. In each unramified source arm \(v(1+U_h^2/R)=\min(0,2v(U_h)-1)\). These values are never positive, so \(N_0\) is integral iff \(U_h\) has positive depth at every arm. Equivalently \([2h]P_0\) reduces to \(O\) at every arm by \(U_h^2=1/x([2h]P_0)\). The exact orders are
\[
\begin{array}{c|rrrrrr}
p&5&163&661&733&1489&1861\\
\operatorname{ord}(P_0)&5&162&21905&44895&(356,778)&27931 .
\end{array}
\]
Thus \(h\) is a multiple of \(L=\operatorname{lcm}(5,81,21905,44895,178,389,27931)=10270488051689719230\).

At the inert source primes \(5,163,661,733,1861\), \(v_p(H)\) is twice the arm depth. Integrality of \(Q_0\) forces positive \(U_i\)-depth and \(2(v(U_i)-v(U_h))\ge15\). If the arm order is \(r\), both indices are multiples of \(r/\gcd(r,2)\); their doubled points are multiples of the same nonzero formal point. On this unramified odd local field the formal logarithm preserves positive depth, which is also the positive depth of \(U_j\) by the square identity. Hence \(v(U_i)-v(U_h)=v_p(i)-v_p(h)\), so \(v_p(i)\ge v_p(h)+8\). In particular \(5^9\mid i\).

At \(p=1489\) both \(U_h\) arms are positive. If both \(U_i\) arms are positive the same argument gives \(v_p(i)\ge v_p(h)+8\). If only one is positive, use \(v(U_j)=c_{\rm arm}+v_p(j)\) on a positive arm, with \(c_{\rm arm}\ge1\) since its doubled order divisor \(178\) or \(389\) is prime to \(p\). The other arm contributes at most zero to \(v_p(I)\); then \(v_p(I)-v_p(H)\ge15\) forces \(v_p(i)\ge16+2v_p(h)\). No positive arm is impossible.

Consequently the six odd-\(R\) Γ conditions force
\[
                      |h|\ge L,\qquad |i|\ge L(R/4)^8 .
\]
When both split \(i\)-arms are positive the latter integer divides \(i\). In the one-positive case one can lose at most the missing order divisor \(178\) or \(389\) from the least common multiple, but gains \(1489^8\). The shift lower bound is a 140-digit integer (463 bits), sharp for **this six-prime subsystem**: \(h=L,\ i=L(R/4)^8\) gives the required depths on both arms. This is not all-place scalar or real-guard admissibility at that particular pair. It rules out \(i=\pm h\) or any fixed multiple \(i=mh\) missing one of the required eighth powers.

## 2. The unchanged physical anchor forces \(v_3(i)\ge32767\)

For four original odd labels, keep \(S=3^{65536}\) exactly and set \(\rho=4096\,\operatorname{normProduct}(\mathrm{labels})+I/S\). FixedAnchorNormDepths318.actual_product_depths gives \(v_3(\operatorname{normProduct})=0\); ScalarIndexValuations318.scalar_norm_three gives \(v_3(I)=2+2v_3(i)\) since \(i\) is even. Below \(v_3(i)=32767\), the second term of \(\rho\) has negative order and cannot cancel the first. The normalized target \(3\rho^2-2\) then has negative odd 3-order with stripped unit \(1\bmod 3\).

Any value of \(x^2+6y^2-2z^2\) with odd valuation in \(\mathbf Q_3\) instead has stripped unit \(2\bmod3\): \(x^2-2z^2\) is an unramified norm of even order when nonzero, and \(6y^2\) has odd order with unit 2. Conversely for \(v_3(i)\ge32767\), \(\rho\) is integral and \(3\rho^2-2\equiv1\bmod3\) is a square. Thus the threshold is **necessary and sufficient for the 3-adic physical anchor**, not just a bound from the preparation lemma. Scaling by \(S^2\) does not change the obstruction. This concerns the literal odd-label branch, not every potential representation of the final polynomial.

## 3. A genuinely different same-cyclic source, with scalar Ready and the actual anchor

From the [materialized old](../../joined-work-20261120/rc-linked-scalar-specialization-r1/ACTUAL-MATERIALIZED-SCALAR-SPECIALIZATION.md) \(h,J\) define
\[
                 h'=71h,\quad i'=301\cdot6^{15}3^{32752}J,\quad n'=1+i'.
\]
These are integer indices on the same generator. The labels are the unchanged positive odd Lucas recipe: first label \(3723\), second \(n'\), \(k=2(n'-2)\), last two \(U_{k+1}(n')\) and \(U_k(n')/(n'-2)\), using \(U_j(n')\) for the Lucas sequence in this sentence only. In particular \(6^{15}\mid i'\), so it is of the original scalarLabel \(0,0,d\) shape. The explicit witnesses supply the two literal arithmetic label relations; they are not identified definitionally with an opaque Classical.choice.

Both multipliers \(71,301\) are units at the original scalar preparation places \(2,3,5,11,17,163,661,733,1489,1861,13,37,53,131\). Both indices remain multiples of the old source formal orders; \(i'\) is a multiple of the old \(h\), though not necessarily of \(h'\). At odd protected places use the formal comparison on the common doubled-order subgroup. The old positive \(Q_0\)-depths persist except at 3 where they remain positive. At 2 the literal \(U_j\) norm and chart bounds depend only on the retained \(v_2(h')=6,\ v_2(i')=22\), giving \(v_2(Q_0)=2,\ v_2(N_0-1)\ge9,\ W\equiv1\bmod64\). These preparations give the same scalar Ready data: \(b\) has square denominator, is locally square at \(2,3,17\) with valuations \(4,2,2\), and \(\delta\) is a square unit at every odd \(\beta\) prime and at 2. At 131, unchanged deeper \(U_h\) and positive \(Q_0\) give \(W\equiv1\bmod131^2\), so the old odd 131-depth remains.

Exact directed intervals give \(-355/1000<H(h')<-354/1000\). The four guards are nonzero by the same five-adic witness: the labels are \((3,1,4,1)\) mod 5, \(h'P_0\) is formal there, and the original guard reductions are \((4,1,1,1)\). PreparedIntegerSource318.scalar_domain gives \(0<b<17\), so \(\delta>0\). The singleton compact set of these actual coefficients in ThreeDetectorUniformFamily318.uniform_family gives the original pre-rows and three strict real domains for \(t\) sufficiently large **at this same \(h'\)**. No other detector Ready, specific contact parameter or detector PointPair is claimed.

The final physical anchor is rational at this alternate index by ordinary Hasse–Minkowski, without changing scale or using rank. Here \(v_3(i')=32767\), and the original odd-label theorem gives \(v_2(\rho)=0\). Thus \(3\rho^2-2\) is square at both 2 and 3. At other finite places the nondegenerate ternary reduction is isotropic and lifts, hence represents every target; the real ternary form is indefinite. The homogeneous four-variable form has a rational point, and its homogenizing coordinate is nonzero by anisotropy of the ternary form over \(\mathbf Q_3\) at zero (the two even terms are an unramified anisotropic binary norm and cannot cancel the odd term). This gives precisely ScalarCompleteSource318.Anchor, not the PointPair inputs of the unchanged complete_at_index.

Finally at \(p=2887\), use the actual \(P_0\) on **both arms**, not arbitrary independent local points. Exact second-order Kummer evaluation gives
\[
                         \delta'\equiv2061318=714p\bmod p^2 .
\]
Here \((5/p)=-1\) and \(\beta\) is square, so \(\delta'\) is not a \(\sqrt5\)-norm and the same Γ fails at \(p\). The old literal scalar had \(\delta\equiv1634\bmod p\), a unit. This is a provably different native source scalar, and a genuine obstruction to inferring a norm just from admissible retuning, the scalar guards, and the original anchor. It is not a rejection of the old scalar, an obstruction to the full Kummer for the new scalar, a rank result, or a final polynomial solution. An admissible index actually satisfying the literal norm is still missing.
