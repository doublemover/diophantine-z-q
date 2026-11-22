# The eight-branch degree-(3,3) stratum is impossible at the fixed original scalar

Keep the literal archived original \(a=0\) scalar \(b\), with its
positive nonsquare \(\beta=204618888056724185\) and positive nonsquare
\(\delta=1-\beta c^2\), not a new specialization. The
[raw fibration](https://github.com/doublemover/diophantine-z-q/blob/26396907b6850a8659e6ecaab31c6b056d66d136/research/quartic-318-326/original-a0-variable-first-no-raw-section/source/original-a0-variable-first-no-raw-section-r1/VARIABLE-FIRST-PARAMETER-NO-RAW-SECTION.md)
uses \(f_\beta(t)=(t^2-\beta)(t^2+3\beta)\) and
\(W^2=\delta f_\beta(t)f_\beta(t')\).
The [separate structural reduction](../original-a0-bidegree-33-finite-feasibility-r1/BIDEGREE-33-FINITE-GEOMETRIC-TEST.md)
shows that two rational degree-three parameter maps \(t,t'\)
have shared odd-branch support of size eight or twelve.
Here the eight-point case is excluded exactly; the twelve-point
case and all individual numerical rational points remain open.

## A genus-three Jacobian forces a rational cyclic 3-subgroup

Let \(H\) be a smooth geometrically integral genus-three curve
over \(\mathbb Q\) with degree-three morphisms \(g_i\) to
smooth genus-one curves whose Jacobians \(E_i\) are rationally
nonisogenous. Put \(J=J(H)\). The canonical polarizations
make \(g_{i,*}\) the dual of \(g_i^*\), and
\(g_{i,*}g_i^*=[3]\). In this prime-degree situation
\(g_i^*:E_i\to J\) embeds \(E_i\).
For a proof, let \(A_i\) be the image abelian variety and
let \(d_i\) be the degree of the induced isogeny \(E_i\to A_i\).
Dualizing its factorization shows that \(g_{i,*}\) factors
through \(A_i^\vee\to E_i\) of degree \(d_i\).
Over the algebraic closure the original curve map agrees
up to translation with the Abel–Jacobi map followed by
\(g_{i,*}\), so \(d_i\mid3\).
If \(d_i=3\), \(H\) would map with degree one to an elliptic
curve, impossible. Thus \(d_i=1\).

Now identify \(A_i\) with \(E_i\). The restriction of the
principal polarization of \(J\) to \(A_i\) is three times its
principal polarization. Moreover the two copies are orthogonal:
\(g_{1,*}g_2^*=g_{2,*}g_1^*=0\), by the rational nonisogeny.
Consequently \(M=A_1\cap A_2\) is a rational finite subgroup
of both \(A_i[3]\), and its geometric order is \(1,3\) or \(9\).
Put \(S=A_1+A_2\) and let \(B=S^\perp\) be its elliptic orthogonal
complement in the principally polarized \(J\).
Under a principal polarization the orthogonal complement
is the kernel of the composed dual of the inclusion;
this kernel is connected because it is dual to a quotient
by an abelian subvariety. Therefore
\(\ker(\lambda_S)=S\cap B=\ker(\lambda_B)\), for the
restricted polarizations.

* If \(|M|=1\), addition identifies \(S\) with \(A_1\times A_2\),
  with the product of their degree-three polarizing line bundles.
  Then \(\ker(\lambda_S)=A_1[3]\times A_2[3]\) has order 81
  and exponent three. It cannot embed in the elliptic
  \(B[3]\), which has order nine.
* If \(|M|=9\), addition \(A_1\times A_2\to S\) has degree nine.
  The pullback polarization has degree 81, so
  \(\deg(\lambda_S)=81/9^2=1\). Then \(S\cap B=0\)
  and addition \(S\times B\to J\) is a split isomorphism
  of principally polarized abelian varieties. A smooth
  geometrically integral curve's Jacobian has an irreducible
  theta divisor (the image, up to translation, of the
  \((g-1)\)-fold symmetric product of its curve); the theta
  divisor of a nontrivial product principal polarization is
  reducible. Hence this case is impossible.

Thus \(|M|=3\), and each \(E_i\) has a rational cyclic subgroup
of order three. This argument uses the rational polarization
and actual elliptic quotient maps, not a guessed deck group
or a geometrical nonisogeny of the two twists.

## Apply it to the actual genus-one forms

If the shared odd branch set in the raw degree-\((3,3)\)
problem has size eight, the common hyperelliptic double cover
has genus three. Its two maps of degree three go to
\(C_1:u^2=f_\beta(t)\) and \(C_\delta:v^2=\delta f_\beta(t')\).
Their Jacobians are
\[
 E'_\beta:\quad Y^2=X(X^2-4\beta X+16\beta^2)
 \quad\text{and its quadratic }\delta\text{-twist}.
\]
As in the raw-fibration proof, \(j(E'_\beta)=2048/3\)
is nonintegral, so the geometric endomorphism ring is
\(\mathbb Z\); the nonsquare twist makes them nonisogenous
over \(\mathbb Q\).

On \(E'_\beta\), the four geometric \(x\)-coordinates
of nonzero 3-torsion modulo sign are the roots of
\[
       3X^4-16\beta X^3+96\beta^2X^2-256\beta^4.
\]
Indeed, for \(Y^2=X^3+a_2X^2+a_4X\) the usual division
polynomial is \(3X^4+4a_2X^3+6a_4X^2-a_4^2\).
With \(X=\beta u\) the polynomial becomes
\(3u^4-16u^3+96u^2-256\), up to \(\beta^4\).
A rational root has denominator dividing three and hence
reduces modulo 5, but the residues at \(u=0,1,2,3,4\)
are \(4,2,3,4,4\), all nonzero.
A rational cyclic subgroup of order three would supply
a rational \(x\)-coordinate (its two nonidentity points
are interchanged at most by negation), so none exists.
This contradicts the genus-three polarization requirement.

The result excludes only the eight-branch stratum of rational
degree-\((3,3)\) parametrizations. It does not test the
genus-five stratum, where the complementary variety to \(S\)
has dimension three and the key elliptic-kernel argument
no longer applies. The modulo-five calculation is on a
fixed normalized polynomial, not a prime test on the
unknown support of the actual scalar or a coefficient search.

~~~sh
sha256sum -c SHA256SUMS
python3 -B replay_three_division.py | cmp - EXACT-THREE-DIVISION.json
~~~
