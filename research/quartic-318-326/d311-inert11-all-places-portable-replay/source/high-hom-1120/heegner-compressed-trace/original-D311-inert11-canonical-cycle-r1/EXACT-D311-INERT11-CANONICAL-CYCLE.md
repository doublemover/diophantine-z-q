# Exact precision-50 canonical lifts from the horizontal 19-cycle

This is a moving-first arithmetic control for the bounded test discriminant \(D=-311\) at 11. Starting with the actual moving optimal embedding of the marked \((2,0)\) level branch in the exact two-path control (c6242b9e), it reconstructs all nineteen **maximal-order** source models modulo \(11^{50}\), without the Hilbert class polynomial, huge 2-power torsion, or any conductor-241 source-building. It does not yet lift the 4,598 conductor-241 flags or evaluate the full local valuation. It does not use or solve the original selected detector discriminant.

## 1. Exact residue path without precision escalation on torsion

Work in \(k=\mathbf F_{11}(s)\), \(s^2=2\), with named \(\sqrt D=2s\). On \(A:y^2=x^3-x\) take \(i(x,y)=(-x,4sy)\) and 11-Frobenius \(\pi\). The exact marked source donor gives
\[
 V=-5i-\pi-5i\pi,\qquad \alpha=(1+V)/2.
\]
It has norm 78 and trace one, with Lie action \((1+2s)/2\); the ordered eigenvalue on the 16-line is 2 and that on the 3-line is 0. Thus the first degree-two horizontal arrow is the even-eigenvalue branch. Since \(\alpha\) has characteristic polynomial \(X^2-X+78\), its reduction on geometric 2-torsion has two distinct eigenvalues; the unique even eigenline is its kernel there.

The replay works with rational endomorphism expressions \(X(x), y\,Z(x)\). The norm-three operator \(\eta=(1+\pi)/2\) has its unique degree-three kernel in the \(\pi=-1\) line. The corresponding normalized Vélu quotient is isomorphic to \(A\) by scale two with differential \(1/2\). This identifies the candidate, and the replay additionally checks \([2]\eta=1+\pi\) as complete rational maps. Thus \(\alpha=1-\eta-5i\eta\) gives the exact degree-78 \(x\)-map, not just a tangent or a torsion sample.

A degree-two quotient with kernel root \(k_0\) on \(y^2=x^3+a x+b_0\) has normalized Vélu \(x\)-map
\[
  \phi_x(x)=k_0+u+d/u,\qquad u=x-k_0,\qquad d=3k_0^2+a.
\]
In passing \(\alpha\) to the quotient, \(\phi_x\circ\alpha_x\) is invariant under the deck involution \(u\mapsto d/u\). Reduce its numerator and denominator by \(u^2=(\phi_x-k_0)u-d\). Each becomes a linear polynomial in \(u\) over the rational function field of \(\phi_x-k_0\). The two coefficient cross-products agree, so their ratio gives the transported \(x\)-map after the shift by \(k_0\). The replay checks this exact cross-product at every step and checks the degree remains 78. Since the transported \(\alpha\) is integral on the quotient, the next even eigenline is recovered as the unique one of the three actual 2-torsion roots at which the reduced \(x\)-map has a pole. No increasing torsion order is used.

The reduced forms for \(-311\) have cardinal 19, and the split prime over 2 is nonprincipal (there is no element of norm 2). Thus the even 2-prime acts in one cycle of length 19 on the maximal CM lattice classes. The residue model need not consist of 19 distinct coarse \(j\)'s. The arrows are distinguished here by the transported endomorphism. The even prime's nineteenth power has the generator
\[
 \mu=(1341-31\sqrt D)/2=686-31\alpha,\qquad N(\mu)=2^{19}.
\]
It is even on the \(\alpha=0\) arm and odd on the \(\alpha=1\) arm. The replay calculates the residue end model of the 19 normalized Vélu arrows, and finds the unique closing scale \(u_\mathrm{cl}\) specified by both the equality of the transported \(\alpha\) \(x\)-maps under scaling and the differential condition \(u_\mathrm{cl}^{-1}=\mu\bmod11\). Its value in basis \(1,s\) is \((10,7)\); the named \(\mu\bmod11\) is \((5,2)\). The ending \(j\)-value alone would not identify that closing isomorphism.

## 2. A unit-derivative closure equation in a short Weierstrass chart

Use the deformation chart
\[
 A_T:y^2=x^3-x+T,\quad T\equiv0\bmod11.
\]
Work in the unramified Witt ring written \(\mathbb Z_{11}[s]\), \(s^2=2\). For a proposed \(T\), lift each of the nineteen recorded simple 2-kernel roots in turn by its cubic kernel equation. Compute the two normalized target short coefficients using Vélu, and repeat. Given the last coefficients \(a',b'\), lift the **named** scale by \(a'u^4=-1\), and define the closure equation
\[
 \mathcal F(T)=b'u^6-T.
\]
These operations are regular on the named residue discs. Each kernel cubic has a unit derivative at the simple root, as does the scale equation; the latter uses \(11\nmid4\) and \(a'\) a unit. Direct exact computations modulo \(121\) give
\[
 \mathcal F(0)\equiv 88+33s\pmod{121},\qquad
 \mathcal F'(0)\equiv 10+7s\pmod {11}.
\]
For the derivative, the replay computes \((\mathcal F(11)-\mathcal F(0))/11\bmod11\); it also verifies agreement with \(\mu/\bar\mu-1\) in this chart. The proof of simple Hensel closure uses the direct unit computation, not an assumed normalization of that ratio. At every lifted digit \(j\), all residues in the error \(\mathcal F(T)\) are divisible by \(11^j\) before the correction. The final error is exactly zero modulo \(11^{50}\).

To identify the computed branch as the **actual** moving maximal-order CM curve, the inert canonical lift of the initial optimal embedding carries the same split even CM 2-prime. Its projected residue sequence must be the uniquely marked sequence just constructed. On that canonical lift the nineteenth ideal is principal, with the named action of \(\mu\) and its residue closing scale. The canonical lift can be written in the displayed short Weierstrass disc: its \(a\)-coefficient can be scaled to \(-1\) with the near-identity fourth root. It is therefore a zero of the same scalar regular equation. The simple Hensel uniqueness in this disc identifies the \(T\) just computed. This argument uses the existence of the inert optimal canonical branch and does not assume a class-polynomial factorization modulo 11.

The specific starting \(T\) is \((44924,13937)\bmod 11^5\) in basis \(1,s\); the attached JSON supplies its full precision-50 value, the nineteen lifted source/target steps, and the closing scale.

Replay from the preserved donor-relative layout with Python 3 and python-flint 0.9.0:

~~~sh
sha256sum -c SHA256SUMS
python3 -B check_D311_p11_canonical_cycle.py | cmp - EXACT-D311-P11-CANONICAL-2-CYCLE.json
~~~

All finite and p-adic arithmetic is exact. Full tame marks for the 241 lifts and the total p11 valuation remain separate tasks.
