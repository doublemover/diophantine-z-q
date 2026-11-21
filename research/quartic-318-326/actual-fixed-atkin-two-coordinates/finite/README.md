# Actual sparse Atkin quotient coordinates at the good prime 13

This is a finite evaluation on the **genuine** lower
\(X_0(205042530)\), with the same level and residue prime
as the cubic receiver. It evaluates weight-zero quotient
coordinates, **not** \(R=\omega(f_N)/\Theta\), \(\pi^\flat\),
the cubic eigentorsor, or the production genus trace.
The tested slice uses a fixed actual supersingular model
and unselected markings, not the selected CM class orbit.

## 1. The actual oriented maximal order and cyclic kernels

Over \(k=\mathbb F_{13}[e]\), \(e^2=2\), take
\(B:y^2=x^3+4x+6\) (equivalently \(x^3-35x-98\)).
It has \(j=5\), the sole geometric supersingular
\(j\) at 13, and has arithmetic 13-Frobenius of
trace zero. In particular square Frobenius is
\([-13]\), so all prime-to-13 cyclic subgroup
**lines** are defined over \(k\) even when individual
generators are not. Use the ordinary normalized degree-two Vélu quotient
\(x'=x+a+b/x,\ y'=y(1-b/x^2)\) in the shifted
root coordinates, followed by the short-model scale.
There are two exact returning quotients:
\[
 \begin{array}{c|c|c|c}
 &\text{kernel x}&\text{scale and tangent}&\text{trace}\\ \hline
 \gamma&3+2e&7+2e&1\\
 J&7&5e&0 .
 \end{array}
\]
The short coefficient identities are directly verified
in the replay. Their traces are determined by adding
the tangent \(s\) to \(2/s\), then selecting the
unique integer in the degree-two Weil bound.
Similarly the tangent of \(\gamma J\) is \(7+9e\)
and its trace is 1 (degree 4).
Cayley–Hamilton and the polarized identity give
\[
 \gamma^2=\gamma-2,\quad J^2=-2,\quad
 J\gamma+\gamma J=J+1 .
\]
The integral ring with basis \(1,\gamma,J,\gamma J\)
has reduced discriminant 13: the Gram determinant of
the integer norm polarization is \(13^2\).
For \(u=r+s\gamma+tJ+b\gamma J\) that norm is
\[
 4\operatorname{Nrd}(u)=(2r+s+b)^2
 +7s^2+2(2t+b)^2-2s(2t+b)+13b^2.
\]
This follows by taking \(I=2\gamma-1\):
\(I^2=-7,\ IJ+JI=2\), and \(IJ-1\) has norm 13
and is orthogonal to \(I,J\).
The ring is therefore the full actual maximal
endomorphism order by
[Deuring's endomorphism theorem](https://doi.org/10.1007/BF02940746).
There is no abstract order identification based
only on having one supersingular \(j\).

At each \(\ell\mid N\), implement the basis by the
literal matrices \(J=\left(\begin{smallmatrix}0&-2\\1&0\end{smallmatrix}\right)\)
and \(\gamma=\left(\begin{smallmatrix}a&1+2c\\c&1-a\end{smallmatrix}\right)\),
with determinant 2 for \(\gamma\), choosing prescribed
roots deterministically. They satisfy the same relations
and are a basis of \(M_2(\mathbb F_\ell)\) in all seven
tested cases including 2. The isomorphism with the
actual torsion action is justified because an
endomorphism killing all \(B[\ell]\) factors through
\([\ell]\), so
\(\operatorname{End}(B)/\ell\simeq\operatorname{End}(B[\ell])\).
A frame change realizing a matrix basis is unique up to
scalar, which preserves all geometric lines.

Enumerating just the norm-\(\ell\) elements modulo
sign gives exactly one isogeny per kernel. This is
not a search over marked vertices: every quotient is
isomorphic to \(B\) over \(k\) (the distinct twist has
opposite trace), and the only automorphisms of \(B\)
are \(\pm1\). The table sizes are
\(3,4,6,8,12,38,2400\).
One specified marked point uses 127 steps to form
all 128 subset quotients, transporting unused marks
by the invertible endomorphism matrices. To compute
the actual \(W\)-orbit, at a used prime replace the
kernel by its dual mark, the **image** of the
rank-one matrix; each subsequent isogeny transports
that image at the other primes too. Hence geometric
\(W\)-orbits are determined independently of any
coincidences of scalar coordinates.

## 2. A literal coordinate canary and a full controlled slice

An actual trace-zero norm-\(251895\) endomorphism
is \((r,s,t,b)=(1,5,-350,-7)\).
Use its kernels at the four primes dividing the
norm, a fixed line at 2, and eigenlines 4 and 1
at 11 and 37 respectively. This gives the literal
marked tuple \((1,2,0,0,11,13,37)\) in the positive
basis-coordinate convention
\(t\leftrightarrow\langle(1,t)\rangle\),
\(\ell\leftrightarrow\langle(0,1)\rangle\).
It is \(W_{251895}\)-fixed by the kernel-image
identity for an endomorphism with square \(-251895\).
This is independent of the mod-61 labelled
canary; it need not identify its reduction from
some particular lifted CM class.

To compute the discriminant products, let
\(\delta_d\) be the product of the actual isogeny
tangents returning \(B/C_d\) to \(B\), with the
chosen sign for each isogeny (an even weight kills it).
Then the discriminant on \(B/C_d\) in the differential
pulling back to the fixed differential is
\(\delta_d^{12}\Delta(B)\). The common discriminant
cancels in every nontrivial character product. A
Walsh transform checks all 127 relevant character
products. For a character with a single negative prime
\(\ell_0\), use the exact rational reciprocal gauge
\[
 \widetilde U_\chi=\ell_0^{-384}
                 \prod_d\Delta_{\rm mod}(dz)^{\chi(d)} .
\]
The matrix formula \(W_{\ell_0}U=\ell_0^{768}/U\)
proves this gauge really transforms by inverse; for
characters with at least two negatives the old
gauge is already correct. In the arithmetic
quotient-discriminant formula the correction for
a singleton is multiplication by \(\ell_0^{384}\),
which reduces to 1 at 13.

For the precise cusp coordinate \(t=(B_{\chi'}/B_w-1)/96\)
of the previous note, the actual fixed label gives
\(t=0\). It is regular at every supersingular label
at 13, since all \(U_\chi\) here lie in \(\mu_7\)
and \(U_\chi^2+U_\chi^{-2}\) never vanishes there.
Among the 17 labels obtained from the fixed one by
replacing its 2399 line by \(0,\ldots,15\), three
invariants (bit masks 3,75,13 in the level prime
order) separate all 17. For example the genuine
lines 0 and 1 give \(t=3,2\) respectively.

On the **entire** 2400-line slice holding the other
six choices fixed, there are 2400 distinct \(W\)-orbits,
but only 2394 distinct tuples even using all 127
symmetric discriminant characters. The six genuine
different-orbit aliases are
\[
 (521,1601),\ (769,2129),\ (847,1768),\
 (902,1594),\ (1125,1239),\ (1370,1407).
\]
For each of these pairs even the **whole oriented**
\(U\)-tuple is identical after some simultaneous
Atkin action; this is stronger than coincident
individually symmetric values. The first small
replay (17 labels) took about 0.25 s and the full
controlled slice about 6.4 s; the latter uses
only the 2400 tested labels and their 127 computed
subset quotients, not the 630 million marked
vertices of the global curve.

This also checks the reviewer's exact birational
pair \(V_1=U_w+U_w^{-1}\) and \(V_2=U_{w'}+U_{w'}^{-1}\),
where \(w'\) is obtained by flipping only the
2-sign. On the quotient the unique cusp poles are
\(m=149299200,3m\) and the first correction of
\(V_2-V_1^3\) gives pole order \(3m-1\).
Thus the ramification index at the restricted
cusp in \(k(V_1,V_2)\subset k(Z)\) divides
\(\gcd(m,3m-1)=1\). The cusp is the only place
above, by the unique pole of \(V_1\), and has
residue degree one, so degree of places gives
\(k(V_1,V_2)=k(Z)\).
Nevertheless the finite scalar pairs take only
16 values on this exact slice. For example lines
521 and 1601 both give \((8,2)\) and have distinct
canonical \(W\)-labels. This is a direct
normalization issue for a plane presentation;
birational coordinates do not separate all its
special branches.

## 3. Why adding these other scalar weights cannot repair the aliases

The norm of the tangent \(\delta_d\) is \(d\bmod13\)
in \(\mathbb F_{13^2}/\mathbb F_{13}\).
One can read it from the actual quaternion norm
form (the checker verifies this on every norm
kernel table), and multiplicativity preserves it
in the subset quotient circuit. Put
\[
 P_\chi=\prod_d\delta_d^{\chi(d)}
  \begin{cases}
  \ell_0^{32},&\text{if a singleton at \(\ell_0\)},\\
  1,&\text{otherwise}.
  \end{cases}
\]
Its norm is 1 after exactly this singleton
normalization, hence \(P_\chi\in\mu_{14}\).
Every normalized product of *one fixed even-weight
level-one form* evaluated on these quotient curves
equals \(P_\chi^{\text{weight}}\) when the form is
nonzero on \(B\). This is because every quotient
curve is the same \(B\) and all changes are the
pullback differential scales. All these even
powers are determined by \(P_\chi^{12}\), since
\(\gcd(12,14)=2\). In particular the natural \(c_4\)
attempt gives no additional information. The
checker independently evaluates its products on
the six aliases and finds no distinctions.
This does not cover general algebraic functions
or genuine local derivative data.

The next possible finite step is to resolve these
branches with the actual marked local
deformations, or supply an invariant rational
expression for \(R\) with correct local
cancellation. The scalar eigenfunction for the
mod-13 cubic receiver remains a different missing
input; no evaluation of it or of a selected
grade-one genus trace occurs here.

    python3 -B check_sparse_atkin_13.py | cmp - EXACT-SPARSE-ATKIN-13.json
    python3 -B check_sparse_atkin_13.py --full-last-slot | cmp - EXACT-FULL-LAST-SLICE-13.json
    sha256sum -c SHA256SUMS

