# Exact dyadic parity of the weighted level-48 reference trace at D = -119

The complete \(\chi_{17}\)-weighted level-48 trace at \(D=-119\),
after descent to the fixed rank-one curve \(E_{-17}\), has **odd
free coordinate**. This is a rational divisibility calculation by
ordinary reduction at 3. It does not follow from the inert 29
nonvanishing check. In particular, the reference trace is not
a rational double modulo torsion. No raw unweighted target trace
or target rank is certified here.

## 1. The actual ten CM inputs at 3 admit a one-polynomial receipt

Use the same degree-two modular map as in the
[complete oriented reference](../../../rc-native-helper-20261120/ct-level48-inert-oriented-cm-D119-pilot-r1/COMPLETE-ORIENTED-INERT-CM-D119-PILOT.md):
\[
 X_0(48): Y^2=X^8+14X^4+1,\quad
 y_{48}=(Y+X^4+1)/2,\quad
 (x,y)=\phi(X,Y)=(y_{48}/X^2,(X-X^{-1})y_{48}/X^2).
\]
The target is \(E_0: y^2=x(x+1)(x-3)=E_{-1}\).
All level structures below use the actual prime ideals in the
maximal order of \(K=\mathbf Q(\sqrt{-119})\), with both 2 and
3 split. The reduced primitive forms give \(h(K)=10\).
The norm-32 element \((3+\sqrt{-119})/2\) proves a prime ideal
\(\mathfrak p_2\) above 2 has class order 5 (no element has norm 2).
The norm-36 element \((5+\sqrt{-119})/2\) gives
\([\mathfrak p_3]^2=[\mathfrak p_2]^{\pm2}\): its trace is
coprime to 6, so its ideal is supported on only one arm at
each of 2 and 3, at exponents 2 and 2. The genus character
\(\chi_{17}\) is positive at \(\mathfrak p_2\) and negative
at \(\mathfrak p_3\), so \([\mathfrak p_3]\) has order 10.

At a prime over 3 use the ordinary component of the
Deligne--Rapoport modular model on which
\(Y=X^4+1\) in this chart. The two components have opposite
signs and the \(w_3\) level operation interchanges them; every
summand lies on the same component because the chosen 3-level is
one of the connected or étale arms at an ordinary split CM prime.
Equivalently the two degeneracy maps \(X_0(48)\to X_0(16)\)
become the identity and Frobenius in opposite orders on
the two components. We may choose the indicated component:
\(\phi w_3=T_0-\phi\), so switching that orientation negates
the weighted sum. Switching the 2-arm by \(w_{16}\) translates
\(\phi\) by a rational 2-torsion point, canceled by the weights.
We fix the 2-arm on which one degree-two horizontal successor
acts by the fourth power of the arithmetic Frobenius at 3.
This is possible since
\([\mathfrak p_3]^4=[\mathfrak p_2]^{\pm1}\);
an inverse Artin convention merely switches the choice.

Put \(t=t_{16}=X-2+3X/y_{48}\), the first tame degeneracy
parameter. Its reduction on the chosen component is \(t=X+1\).
The first and second tame degeneracies at levels 16, 8, 4 are
\[
 \big(t^2/(t+2),t(t+4)\big),\quad
 \big(t^2/(t+4),t(t+8)\big),\quad
 \big(t^2/(t+16),t(t+16)\big).
\]
The exact reference explains the \(+8\) in the second level-8
map, recovered from the Atkin--Lehner involutions; these are
ordered degeneracies, not unordered \(j\)-edges.
For \(0\le k\le3\), let \(A_k(t)\) be the \(k\)-th successive
degree-two edge parameter in a cyclic 16 flag: take the second
degeneracy \(k\) times and then the first \(3-k\) times. Over
\(\mathbf F_3\) the ordinary horizontal CM flags satisfy
\[
 A_{k+1}(t)=A_k(t)^{81}\quad (k=0,1,2),\qquad t^{3^{10}}=t.
\]
Indeed Shimura reciprocity on the tame level-16 flags at the
unramified Hilbert class place is the ideal action just calculated.
Our split CM curves are ordinary and potentially good; their
tame level specializations have neither cusp nor supersingular
\(j\). Consequently the relevant edge chart coordinates
are finite, and none of their tame degeneracy denominators is zero.

The exact \(\mathbf F_3[t]\) gcd of these four polynomial
conditions, with fractions cleared, is
\[
 t(t^2+1)(t^2-t-1)H(t),
 \qquad
 H=t^{10}-t^9+t^8+t^7+t^6+t^5+t^4-t^3-t^2+1.
\]
The first factor gives a cusp; the roots of the two quadratics
give \(t_2=-1\), hence \(j=0\), supersingular in characteristic
three. \(H\) is irreducible (degree-ten Frobenius and the tests
at degrees 2 and 5). Thus one actual \(t\) is a root of \(H\);
its 10 distinct Frobenius conjugates account for the entire
actual Hilbert class orbit. No general injectivity assertion
for CM reduction or choice of a seed class from the polynomial
is needed. The \(\chi_{17}\)-positive half can be labeled as the
orbit under the square of Frobenius, up to interchanging
the two halves.

## 2. A local torus unit detects the free parity

The target \(E_0\) at 3 is minimal split multiplicative,
type \(I_2\): its discriminant has valuation 2, \(c_4=208\)
is a unit, and the tangents at the node split. Write
\(v=X-X^{-1}\); on the ordinary component,
\(x=v^2-1,\ y=vx\) modulo 3. This is the nodal
normalization; the multiplicative identity coordinate is
\[
 g(t)=\frac{v-1}{v+1}
     =\frac{t^2+1}{t^2-t-1}.
\]
Using the reciprocal choice would not affect the result.
Every summand is on the identity smooth locus since its
ordinary \(t\) avoids the two quadratics. The torus point
for the sum on one genus half is the norm
\[
 u=\operatorname{N}_{\mathbf F_{3^{10}}/\mathbf F_9}g(t).
\]
The replay gives \(u^4=-1\). Frobenius interchanges the halves;
therefore the weighted trace reduces to \(u/u^3=u^{-2}\)
or its inverse, of exact order 4 in the norm-one torus.

The fixed twist \(E_{-17}: y^2=x(x+17)(x-51)\) is the
unramified nonsplit twist at 3, since \((17/3)=-1\).
The torus calculation just made is exactly its identity
reduction in \(\mathbf F_9\): the Galois generator acts by
inversion under the twist. The component group has order two,
with a rational 2-torsion point in its nonidentity component.
For example \((0,0)\) reduces to the node on this minimal
Weierstrass equation. Thus any rational local double is a
double of a point of the identity component after subtracting
that rational 2-torsion as needed. In the identity torus
such a double reduces to a square. A rational torsion point
that belongs to the identity component has residue of order
dividing two (odd torsion cannot survive the order-four torus,
and no rational torsion has order divisible by four).
For the latter fact, on \(E_0\) halves of its three nonzero
2-torsions require respectively \(\sqrt{-3}\), \(i\), or
\(\sqrt3\); none is in \(\mathbf Q(\sqrt{17})\) where
\(E_{-17}\) untwists. Hence within the identity component,
\(2E_{-17}(\mathbf Q_3)+E_{-17}(\mathbf Q)_{\mathrm{tors}}\)
can reduce only to torus squares. The weighted residue of
order four excludes this. In particular the rational weighted
reference is not divisible by 2 modulo rational torsion.

The [explicit height comparison](../original-detectors-chi17-both-weighted-r1/BOTH-ACTUAL-CHI17-WEIGHTED-TRACES.md)
puts the reference and both selected weighted traces on the
same fixed rank-one curve, with free coordinates \(m_7,m_i\):
\[
 |m_i|=2^{\omega(s_i)-1}\sqrt{\mathcal L(s_i)}\,|m_7|.
\]
Thus \(v_2(m_7)=0\), and for those two selected arms the exact
first free depths are \(v_2(m_i)=\omega(s_i)-1\).
The separate rational-double statement for selected supporting
graphs applies to the production \(m_i\), not to \(m_7\);
there is no contradiction.

The reference also shows why odd class number after removing
the genus factor does **not** by itself imply that every
proper weighted genus component is divisible by that genus
factor on its rational quadratic eigenside. Here the factor
is \(2\), the residual class number is \(5\), and the nontrivial
character fails that divisibility. This is the first
two-prime \(n\equiv23\bmod24\) control with odd residual class
number: the smaller two-prime value \(95\) has class number
8, while 23, 47, and 71 are prime. This is not a no-go for
a more specific auxiliary-field graph or for analyzing all
proper competitors on such graphs.

## Replay

Run \(\texttt{python3 -B replay_reference_parity.py | cmp - EXACT-REFERENCE-PARITY.json}\)
and \(\texttt{sha256sum -c SHA256SUMS}\). The replay uses only
integer polynomial arithmetic in the standard library. It
also checks the small reduced form counts.
