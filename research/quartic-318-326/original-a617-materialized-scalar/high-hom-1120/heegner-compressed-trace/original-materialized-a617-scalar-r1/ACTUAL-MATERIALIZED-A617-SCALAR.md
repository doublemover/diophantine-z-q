# An exact admissible scalar index for the original a=617 source

The companion JSON specifies one finite pair \((h,J)\), not just a compatible local family. It uses the actual original elliptic generator, scalar coefficients and Lucas labels of the admissible input \(a=617\). No rational ordinate pair, root sign, anchor or simultaneous three-detector index is claimed.

## Compact specification

Write \(i=6^{15}3^{65536}J\), \(s=1+i\), \(k=2(s-2)\), and use \(U_0=0,U_1=1,U_{j+1}=sU_j-U_{j-1}\) for the integer Lucas sequence. The four labels are
\[
 (3723\cdot1235^2,\ s,\ U_{k+1},\ U_k/(s-2)).
\]
These are the original labels, not independently specified residues. The last quotient is an integer because \(U_k\equiv k\pmod{s-2}\). All labels are positive by the increasing positive Lucas recurrence at \(s>2\), and \(s\ne1\). Their index need not be expanded. The associated \(R,\beta_{\rm raw},K=1+2448\beta_{\rm raw}\) are exactly those in [the degree-two graph note](../original-a617-quadratic-graph-genus-one-r1/ACTUAL-A617-QUADRATIC-GRAPH-AND-SIGN.md).

The checker finds verified finite annihilators \(n_{p,\mathfrak p}\) of the original \(P_0=(1+\sqrt2,2\sqrt2)\) on \(y^2=x^3-(3-\sqrt2)^2x\), at every odd prime in the printed set and in each split arm. Large candidate annihilators enter only after an exact group-law computation gives the identity. Define
\[
 h=\operatorname{lcm}(64,(n_{p,\mathfrak p})_{p,\mathfrak p})
       \prod_{p\ne2}p^{\lfloor v_p(R)/2\rfloor},\qquad
 J=h\prod_p p^{\lceil(15v_p(R)+1)/2\rceil}.
\]
The products use that printed set of primes. This very \(h\) passes the real margin on the first test, so no search over progression choices remains. In particular \(h,J,i\) have bit lengths \(201,1309,105220\).

## Real guards and original scalar preparation

At the inert prime \(59\) the same source point has exact order 60. Thus \([h]P_0=[i]P_0=O\) on reduction and \(s\equiv1\pmod{60}\). In this quotient the Lucas sequence has period 6 and \(k\equiv4\pmod6\); dividing by \(s-2\equiv-1\pmod{60}\) is valid. The four labels reduce to the classes of \((3723\cdot1235^2,1,-1,1)\). On each guard the rational coefficient of \(1/x([-2\ell]P_0)\) reduces to \(8,32,32,32\), respectively; the shifted \(1/x([2h\ell]P_0)\) reduces to zero. Hence the actual guard difference is nonzero. The exact 4096-bit directed real calculation gives
\[
 \mathrm N\bigl(2y([h]P_0)/(x([h]P_0)^2+(3-\sqrt2)^2)\bigr)
 \in[-217085903041018561,-217085903041018560]/2^{64}.
\]
It follows that the absolute margin exceeds \(1/100\). With the nonzero labels and \(s\ne1\), the original `PreparedIntegerSource318.scalar_domain` gives \(0<b<17\) for the exact scalar.

Let \(U_h\) now denote the original elliptic chart, not the Lucas sequence. In the packed expression
\[
 \mathcal N=\mathrm N(1+U_h^2/R),\quad
 Q=R^{-15}\mathrm N(U_i/U_h),\quad W=\mathcal N^2+RQ^2,
 \quad \mu=b/17=\beta_{\rm raw}(12W/K)^2,
\]
\(\mathcal N\equiv1\) and \(Q\equiv0\) at every printed prime. For each odd prime the extra \(p^{\lfloor v_p(R)/2\rfloor}\) after the finite annihilators makes \(2v_{\mathfrak p}(U_h)>v_p(R)\); the good unramified formal logarithm then gives \(v_p(Q)=2v_p(i/h)-15v_p(R)>0\). At 2 use the original dyadic chart and ratio depth for \(64\mid h\), as in [the existing local construction](../../../joined-work-20261120/rc-linked-scalar-variable-index-auxiliary-r1/ACTUAL-VARIABLE-SCALAR-AUXILIARY-PLACE-INDEPENDENCE.md). Thus \(W\equiv1\) throughout the actual first support; the square denominator and prepared 2/3/17 local conditions follow from \(\beta_{\rm raw}\equiv1\bmod8\), \(\beta_{\rm raw}\equiv2\bmod3\), \(\beta_{\rm raw}/17\equiv1\bmod17\), and the exact factorization. In particular \(\delta=1-\mu\) is a square at 2,3 and every prime of \(\beta\). At 5,13,47 the exact \(\delta\) residues are 2,4,46. In particular this \(\delta\) is not a rational square. Its global squarefree numerator is not computed.

Replay from this folder:

```sh
sha256sum -c SHA256SUMS
python3 -B check_materialized_a617_scalar.py | cmp - EXACT-MATERIALIZED-A617-SCALAR.json
```

The only executable external input is a checksum-pinned sibling-lane Python donor, from which the script extracts five named arithmetic definitions without running its top-level search. The local graph theorem applies to this actual scalar. Neither the old two-phase existential proof nor this calculation gives its global sign or a rational point.
