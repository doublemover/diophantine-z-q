# The unchanged selected height metric has curvature at most −64

This is a bounded arithmetic sharpening of the selected same-A reverse
comparison for the literal 318 and 326, not a new geometric or native
theorem. It preserves the exact \(D=210\) surface and the normalizations
of the [reviewed +22 proof and its archived reverse background](https://github.com/doublemover/diophantine-z-q/tree/25f050304eb7e9e124bd899dc8c83699b8edf273/research/quartic-318-326/original-same-a-finite-cluster-gain22).
Neither the published +64/+22 proof nor the native +120 consumer is
changed. The distinct modular Jacobian and the rational-point
construction are unaffected.

Let \(b=(0,32,-343,76832)\), \(r_i=|t-b_i|\), \(r=|t|\),
\(w=(1,1,1/7,1/80)\), and \(U=960+\sum_iw_i r_i\). The old test metric
is exactly \(g_0=U|dt|^2/\prod_i r_i\) pulled back to the compact curve.
In a simple finite root coordinate \(t-b_i=z^2\), the root singularity
of the denominator cancels and \(r_i=|z|^2\); at infinity \(t=z^{-2}\),
and the metric coefficient is
\[
\frac{4(960|z|^2+\sum_iw_i|1-b_i z^2|)}{\prod_i|1-b_i z^2|}.
\]
Both are smooth positive. Off the five branches, set \(N=2U^3(-K_{g_0})\).
Because \(\Delta r_i=1/r_i\) in the Euclidean \(t\) coordinate and
\(\Delta\log r_i=0\), the self terms in \(U\Delta U-|\nabla U|^2\) cancel.
For \(i\ne j\) the cross term is
\(r_i/r_j+r_j/r_i-2\langle\nabla r_i,\nabla r_j\rangle
= (b_i-b_j)^2/(r_i r_j)\). Hence
\[
N=960\sum_i w_i\prod_{j\ne i}r_j+
\sum_{i<j}w_iw_j(b_i-b_j)^2\prod_{\ell\notin\{i,j\}}r_\ell .
\]
All terms are nonnegative. This is the identical earlier formula.

The independent lower calculation first reproduces the seven isolated
radial lower bounds for \(-K\ge7\) (the smallest is
\(175104000/23639903>7\)); along with the exact finite divisor this
already gives the proposed strict +13 without changing definitions.
For the stronger bound, use **all** terms of \(N\). On a closed radial
interval \([x,y]\), set
\[
 d_i=\max(0,x-|b_i|,|b_i|-y),\qquad
 U^+=960+\sum_iw_i(y+|b_i|).
\]
The reverse and forward triangle inequalities give \(r_i\ge d_i\) and
\(U\le U^+\) for every argument of \(t\). Thus substituting the
\(d_i\) in the numerator and \(U^+\) in the denominator is a true
simultaneous lower bound, not a point sample. With \(D=560\) and
\(W_i=Dw_i\), the exact ratio reads
\[
\frac{D(960D\sum_i W_i\prod_{j\ne i}d_j+
 \sum_{i<j}W_iW_j(b_i-b_j)^2\prod_{\ell\notin\{i,j\}}d_\ell)}
 {2(960D+\sum_iW_i(y+|b_i|))^3}.
\]
Bisection of \([0,10^6]\), keeping a cell precisely when its integer
numerator is at least 64 times its denominator, gives the 44 contiguous
rows in EXACT-CURVATURE.json. The first left and final right endpoint
and all consecutive endpoints are checked. For \(r\ge10^6\) all four
\(r_i/r\ge9/10\), and \(U/r\le11/5\); use the first sum alone to get
\[
 -K_{g_0}\ge
 \frac{960(1207/560)(9/10)^3}{2(11/5)^3}>64 .
\]
No condition on the argument of \(t\), no sampling near a branch, and
no floating-point rounding are used. The branch values follow by
continuity.

On the same compact curve take the minimum of the smooth ratio
\(f=h_{\mathrm{hyp}}/g_0\). Since the hyperbolic curvature is −1,
\(f=-K_{g_0}+\frac12\Delta_{g_0}\log f\); hence \(\min f\ge64\).
The original Petersson norm for \(Q=(dt)^2/\prod_i(t-b_i)\) is
\(4/(Uf)\) not \(1/(Uf)\). The unit disk's hyperbolic coefficient at
the center is 4 in the original convention. Also \(U\ge 2\max(32,r)\)
by \(r+r_1\ge2r-32\), \(r+r_1\ge32\) and the constant 960.
Thus the **same** ordered sections \(32D_0^2Q,D_0^2tQ\)
(\(D_0=2765952000\)) under Yuan's raw \(\Psi^{-1}(210\cdot)\) map
have archimedean maximum at most \(420D_0^2/64\).
The reviewed common rational integral divisor
\(C=4D_0^2/25725=1189580636160000\) makes the finite norm at most 1
after dividing both sections by \(C\), without changing the ratio
\(s=t/32\). It follows by the same product formula and same stable
Hodge degree that
\[
 h(s)\le2h_+(A)+\log(2701125/64)<2h_+(A)+11.
\]
For strictness the replay compares \(2701125/64\) with
\((1957/720)^{11}<e^{11}\), using the partial exponential sum
through \(1/6!\). The absolute-value normalizations and all geometric
assumptions are precisely those of the signed +22 comparison.
