# A dyadic genus-half logarithm from bounded jets, not a class list

Fix either actual original selected arm \(n=17s\equiv23\bmod24\) of
the [both-weighted construction](../original-detectors-chi17-both-weighted-r1/BOTH-ACTUAL-CHI17-WEIGHTED-TRACES.md).
Let \(K=\mathbf Q(\sqrt{-n})\) and \(H\) be its Hilbert class
field. Write \(P\) for the untwisted *unweighted* Hilbert trace
on \(E_0=E_{-1}\), and \(R\) for its \(\chi_{17}\)-weighted
counterpart. The half-orbit sum \(A\) satisfies \(2A=P+R\).
This note gives a conditioned finite readout that would detect
nonzero \(P\) modulo torsion. It does not supply the needed
half-orbit jets for a selected \(n\), or a target point or rank.

## 1. Exact target precision

All curves use \(E_0:y^2=x(x+1)(x-3)\). Ordinary complex
conjugation and the element of \(\mathrm{Gal}(K(\sqrt{17})/K)\)
flipping \(\sqrt{17}\) have product acting as \(-1\) on \(A\).
Indeed conjugation exchanges the two genus halves under the
exact Fricke rule \(\phi w_{48}=T_3-\phi\) because
\(\chi_{17}(\mathfrak n)=-1\); the translate \((h(K)/2)T_3\)
vanishes by genus divisibility on the actual support.
Under the twist by 17, \(A\) is therefore a point \(A^\#\)
of \(E_{-17}\) over \(\mathbf Q(\sqrt{-s})\), and \(R^\#\)
is rational on the fixed \(E_{-17}\).
All the fields here split at 2. This is a statement about the
same half of the same CM orbit; it does not replace \(n\).

Let \(G_*\) be a generator of the free part of \(E_{-17}(\mathbf Q)\),
known rank one by the separate weighted trace comparison.
The point
\[
 G=(-169/25,\ 7904/125)
\]
has odd free coordinate: in the Kummer pair \((x-51,x+17)\)
it has classes \((-1,1)\), distinct from the rational torsion
classes \( (1,1),(-51,17),(-17,1),(3,17)\).
These are all the classes modulo squares: on \(E_0\) its
three two-torsion directions can be halved only over fields
containing \(\sqrt{-3},i,\sqrt 3\), none in the untwisting
field \(\mathbf Q(\sqrt{17})\), and odd torsion is a double.
The exact double of \(G\) gives
\[
 z(2G)=-2817953840/3381886431,\qquad v_2(z(2G))=4 .
\]
For the formal parameter \(z=-x/y\), \(\log(2G)=z(2G)+O(z(2G)^3)\)
with odd denominators; thus \(v_2(\log G_*)=3\). Twisting
the differential by a unit at 2 does not change depths.

The calibrated [reference](../original-detectors-chi17-reference-parity-r1/EXACT-D119-WEIGHTED-SEED-IS-ODD.md)
now gives \(R^\#=mG_*+\text{torsion}\) with
\(v_2(m)=\omega(s)-1\).
If \(P\) is torsion, \(2\log A^\#=\log R^\#\) at either split
2-place, and in particular
\[
                     v_2(\log A)=\omega(s)+1 .
\]
This uses an exact equality of logarithms and needs no
hypothesis about torsion growth or divisibility over the
quadratic compositum. Set \(k=\omega(s)+2\). A residue
\(\log A\bmod 2^k\) not of valuation \(k-1\) disproves
torsion of \(P\), including a zero residue. Equality of that
valuation is inconclusive. The two arms can be checked
independently; a flag on one does not establish the other.

## 2. Specify the unit dyadic arm and the local branch

Choose the split dyadic level arm for which every horizontal
degree-two edge parameter \(t_2\) is a unit. For ordinary integral
\(j=(t_2+256)^3/t_2^2\) with \(v_2(j)=0\), the two possible
depths of \(t_2\) are 0 and 12, and reversal \(w_2(t_2)=4096/t_2\)
interchanges them. On the ordinary parts these are the
connected and étale modular components: the first and second
degeneracies are identity and Frobenius in one order or the
other. Repeated quotients by one of the two split CM
2-ideals preserve its connected/étale type. Thus reversing
the full cyclic-16 flag by \(w_{16}\) chooses the unit arm
uniformly. Changing to this arm does not change the logarithms
of any sums, since \(\phi w_{16}\) is a torsion translate of
\(\phi\).

Using the ordered degeneracies in the
[fixed level-48 reference](../../../rc-native-helper-20261120/ct-level48-inert-oriented-cm-D119-pilot-r1/COMPLETE-ORIENTED-INERT-CM-D119-PILOT.md),
all the successive \(t_4,t_8,t_{16}\) are then units. In
fact the second tame degeneracy at each of these levels is
\(v\mapsto v(v+c)\) with \(v_2(c)>0\), so an input of strictly
positive or negative depth cannot have a unit second output.
The 3-isogeny is prime to 2, preserves the ordinary arm, and
so its level-16 parameter \(t_{16}'\) is also a unit.

In the fixed chart write \(y_{48}=(Y+X^4+1)/2\). The peer
parameters and equation give
\[
 t_{16}=X-2+3X/y_{48},\quad
 t_{16}'=(y_{48}-2X-1)/X,\quad
 y_{48}^2-(X^4+1)y_{48}-3X^4=0 .
\]
Now \(y_{48}=(t_{16}'+2)X+1\). If \(v_2(X)>0\) this
would make \(t_{16}\) nonunit, and if \(v_2(X)<0\) it makes
\(X\) the unique dominant term of \(t_{16}\), also impossible.
Thus \(X\) is a unit, and the same quadratic equation makes
\(y_{48}\) a unit. Its two residue roots are \(1,X^4\); the
root \(1\) would give \(t_{16}\equiv0\), so \(y_{48}\equiv X^4\)
and \(X^4-1\) is a unit. This pins a single root
without choosing any square-root sign separately.

Put \(B=X^4-1\) and \(\mathcal R=\mathbf Z_2[X,X^{-1},B^{-1}]\),
and take its 2-adic completion. In it the actual target
\(x=y_{48}/X^2\) is the unique branch
\[
 x=X^2+\sum_{\ell\ge1}(-1)^{\ell-1}
       C_{\ell-1}4^\ell (B/X^2)^{-(2\ell-1)},\qquad
 y=(X-X^{-1})x
\]
where \(C_j\) are Catalan numbers. Substitution is exact:
\(a=x-X^2\) solves \(a^2+(B/X^2)a-4=0\).
At every marked ordinary point, \(x+1\) is a unit and the
image is on the smooth identity locus of the additive
special fiber of the minimal target.

## 3. A small rational function for the local logarithm

Write \(a=x^2+3,\ b=3x^2-4x-3\). The duplication formula gives
\[
            z(2\phi)=2W,\qquad
 W=\frac{y a^2}{8y^4-4bxy^2+b a^2}\in\widehat{\mathcal R}.
\]
The denominator reduces to \(B^3\) in the chosen branch, a
unit in \(\mathcal R/2\). Thus \(2\phi\) is in the formal
group. For this Weierstrass model its invariant differential
in \(z\) is integral and even: if
\(w=-1/y=z^3(1+O(z^2))\),
\(w=z^3-2z^2w-3zw^2\) and
\(\omega=(z w'/w-1)dz/2\). Hence the logarithm is a sum
of odd powers with odd denominators. Consequently
\[
 L_k(X)=\frac12\log(2W)
       =\sum_{j\ge0}\frac{b_{2j}}{2j+1}
                       2^{2j}W^{2j+1}\pmod{2^k}
\]
where \(\omega=(\sum b_{2j}z^{2j})dz\), and only \(2j<k\)
are required. This computes \(z/2\) directly; if one computes
\(z\) first it requires precision \(2^{k+1}\).
The logarithm on the left means the elliptic formal logarithm
with input parameter \(2W\), not a multiplicative logarithm.

Here is a uniform simple size bound. Assign a Laurent monomial
\(X^a B^{-b}\) cost \(|a|+b\), and let \(\mathcal R_d\)
be the \(\mathbf Z_2\)-span of cost at most \(d\);
costs add under products. At dyadic precision weight \(v\),
the expansion of either of \(x,y\) has cost at most \(3v+3\)
above. The numerator and denominator polynomials in \(W\) have
degrees at most 5 and 6 in \(x,y\), respectively, so their
weight-\(v\) costs are at most \(3v+15\) and \(3v+18\).
For its denominator \(D_0\), \(D_0/B^3-1\) is in
\(\sum_{v\ge1}2^v\mathcal R_{24v}\): the zero-weight
difference is an even polynomial in the same ring, and can
be moved to weight 1. A geometric inverse preserves this
slope. Thus \(W\) has costs at most \(24v+18\), and
\(2^{m-1}W^m\) likewise has cost at most \(24v+18\) at
its total weight \(v\). In particular
\[
               L_k=C(X)/(X^{24k}B^{24k}) \pmod{2^k},
               \quad \deg C\le 144k .
\]
The loose linear bound is sufficient. Bounds count the
rational function and its jets, not the cost to obtain
any CM coefficient. The first residue alone is automatic:
\(L_1=X/(X+1)^2=(X+1)^{-1}+(X+1)^{-2}\) over
\(\mathbf F_2\), an Artin--Schreier difference. Its sum on
a Frobenius-stable genus half is zero.

## 4. Exactly what class polynomial data suffice

For the chosen split embedding at 2, let \(H_+(X)\) be the
monic product over the \(\chi_{17}\)-positive half of the
actual marked class orbit, retaining multiplicities.
The local decomposition group preserves that half since
\((17/2)=+1\); thus the coefficients are in \(\mathbf Q_2\)
and are integral since all roots are units. Both
\(H_+(0)\) and \(\operatorname{Res}(H_+,B)\) are units,
as just proved pointwise. This holds even if a root value
has multiplicity. The full trace required above is
\(\sum_{H_+(x)=0}L_k(x)\) with those multiplicities.

Here is an exact compact implementation over \(\mathbf Z/2^k\).
Write \(a=b=24k\) and separate
\(L_k=L_\infty+A_0/X^a+A_B/B^b\) by coprime monic
division; \(B(0)=-1\). The polynomial part \(L_\infty\)
has degree at most \(24k\) and its trace is obtained by
Newton sums using the first \(24k\) leading coefficients
and the known degree of \(H_+\).
For the proper parts the residue theorem gives the negatives of
\[
 [X^{a-1}](A_0H_+'/H_+\bmod X^a),\qquad
 [X^{4b-1}](A_BH_+'/H_+\bmod B^b),
\]
respectively. Indeed \(H_+'/H_+\) has the roots with
their multiplicities as residue divisor. After reducing
the numerator at a pole divisor, the coefficient of \(X^{-1}\)
at infinity of the resulting rational function is the sum
of its finite residues; for the monic powers this is the
displayed coefficient. No inversion of the discriminant
of the pole polynomial is involved. In particular the
four \(B\)-roots need not be separated over a ramified
extension. Safety of the inversions follows exactly from
the two unit resultants. To construct \(H_+'\) in these
residue rings, request \(H_+\bmod X^{a+1},B^{b+1}\);
differentiating unknown multiples then gives zero in the
required smaller rings.

Thus bounded jets (and a short leading segment) suffice
instead of a full class list. They are jets of the actual
*relative marked* CM polynomial, not of an ordinary
unoriented Hilbert class polynomial. No source-tunable
formula or certified fast evaluation of these jets is
currently known here. Zeroth norms of modular units and
their ideals alone do not give these differentiated jets.
