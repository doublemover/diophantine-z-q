# No bidegree-(2,2) rational parametrization on the original fixed raw companion surface

Let \(\beta>0\) be a rational nonsquare and \(\delta>0\) a rational
nonsquare, and set \(f_\beta(t)=(t^2-\beta)(t^2+3\beta)\). Then there
are no \(t,t',W\in\mathbb Q(z)\) such that \(t,t'\) each have degree
exactly two as rational maps \(\mathbf P^1_z\to\mathbf P^1\) and
\[
                     W^2=\delta f_\beta(t)f_\beta(t').
\]
This applies to the **unchanged numerical original** input-0 \(b\):
the [entire first-line obstruction](../original-a0-variable-first-no-raw-section-r1/VARIABLE-FIRST-PARAMETER-NO-RAW-SECTION.md)
identifies these raw equations with the original PointPair and proves
that the actual \(\delta=1-b/17\) is positive nonsquare at the fixed
literal \(a=0,h,J\), using its actual 181 residue. The theorem concerns
rational parametrizations of this fixed surface, not its individual
rational points.

## 1. The common double cover and the forced Klein four group

Form the curve \(H\) with function field
\(\mathbb Q(z)(u)\), \(u^2=f_\beta(t(z))\). This is a genuine
geometrically integral double cover: otherwise \(t(z),u(z)\)
would give a nonconstant map from \(\mathbf P^1\) to the
genus-one curve \(C_1:u^2=f_\beta(t)\), impossible. The
relation also gives \(v=W/u\) with \(v^2=\delta f_\beta(t')\),
so \(H\) maps to both \(C_1\) and \(C_\delta\).
Each map has degree two (the extensions over \(\mathbb Q(t)\)
or \(\mathbb Q(t')\) have total degree four and each intermediate
genus-one field has degree two). The deck automorphisms \(s,s'\)
of these maps are defined over \(\mathbb Q\), commute with the
hyperelliptic involution \(\iota\) (the latter reverses both
\(u,v\) while fixing \(z\)), and neither equals \(\iota\).
Write \(S,S'\) for their images on the rational \(z\)-line.

The branch points of \(H\to\mathbf P^1_z\) are precisely the
unramified preimages under \(t(z)\) of the four roots of
\(f_\beta\). The two critical values of the degree-two map are a
Galois-stable set. Since the four roots are two nonrational
quadratic pairs, either none or two of the two critical values
are among them. Thus there are eight or four branch points and
\(g(H)=3\) or \(1\). Genus one is impossible: the two degree-two
maps would make its Jacobian isogenous to both \(E'_\beta\) and
its \(\delta\)-twist, where \(E'_\beta\) has \(j=2048/3\).
These are nonisogenous over \(\mathbb Q\) because \(\delta\) is
nonsquare and the geometric endomorphism ring is \(\mathbb Z\).
This Jacobian calculation uses the already proved exact
genus-one models of \(C_1,C_\delta\).

Thus \(g(H)=3\). In \(\operatorname{End}^0_\mathbb Q J(H)\) the
projectors \(e=(1+s)/2\) and \(e'=(1+s')/2\) have images
isogenous to \(J(C_1)\) and \(J(C_\delta)\), respectively.
Both cross-compositions are zero, as they factor through a
rational Hom between nonisogenous elliptic curves.
Hence \(s,s'\) commute on \(J(H)\) and also on the curve:
an automorphism acting trivially on differentials fixes the
canonical map, hence is at worst \(\iota\) on this hyperelliptic
curve, and \(\iota\) acts as \(-1\). The product \(ss'\) has
one invariant differential (the common minus space of \(s,s'\))
and so is itself bielliptic. In particular \(s,s',ss'\) are
distinct from the hyperelliptic involution, which has zero
invariant differentials. The induced group
\(\langle S,S'\rangle\) on \(\mathbf P^1_z\) is therefore
the Klein four group. Each nontrivial element acts without
fixed points on the eight branch points. Indeed a bielliptic
involution on a genus-three curve has four fixed points by
Riemann–Hurwitz; its image on the \(z\)-line has exactly two,
so each of those two must have two geometric points above it
and cannot be a branch point. Consequently the eight branch
points are exactly two free orbits of the Klein four group.

## 2. Rigidity of the two branch-pair quotients

Project the two free orbits to the \(t\)-line, that is take
the quotient by \(S\). They become a Galois-invariant
partition of the four roots of \(f_\beta\) into two pairs.
The Galois action on these roots contains the two independent
single transpositions exchanging the real pair and the imaginary
pair: the classes \(\beta,-3\beta\) are independent in
\(\mathbb Q^\times/\mathbb Q^{\times2}\).
A single transposition cannot exchange two whole two-element
blocks, so each of these transpositions preserves both blocks.
Therefore the blocks must be exactly the two quadratic pairs.
Since \(S'\) exchanges the members of each such pair, its
induced Möbius involution on \(\mathbf P^1_t\) is \(t\mapsto-t\):
both Möbius maps agree on more than two distinct geometric points.
On the \(t'\)-line the identical argument with \(S,S'\)
exchanged gives \(t'\mapsto-t'\).

Put \(x=t^2/\beta\) and \(x'=t'^2/\beta\). Both generate the
same invariant field of the Klein four group, so \(x'=M(x)\)
for a rational Möbius map \(M\). The two orbits show that \(M\)
preserves the unordered pair \(\{1,-3\}\).
Moreover \(\mathbb Q(z)=\mathbb Q(x)(t,t')\) because \(t,t'\)
generate the distinct quadratic subfields of the Klein cover.
Its two defining characters have branch sets
\(\{0,\infty\}\), \(M^{-1}\{0,\infty\}\); these share exactly
one point. In detail the normalization of this cover is
geometrically integral of degree four, and has ramification
index two above each member of the union. Genus zero by
Riemann–Hurwitz forces the union size to be three. The quadratic
factors \(\beta\) in \(t^2=\beta x,\ t'^2=\beta M(x)\) change
no branch loci.

## 3. Four transforms and their exact constants

Specify whether \(M\) fixes or exchanges \(1,-3\), and specify
the sole element of \(\{0,\infty\}\) that maps into this same
set and its image. These eight interpolation problems are
rigid (three distinct input points), and the maps that preserve
the whole \(\{0,\infty\}\) do not qualify. Exactly four remain.
For \(F(x)=(x-1)(x+3)\) and \(M=(ax+b)/(cx+d)\), the
polynomial \((cx+d)^2F(M(x))\) is \(KF(x)\); the constants
for the displayed matrices are

| \(M(x)\) | \(K\) |
|---|---:|
| \((3-2x)/x\) | \(-3\) |
| \(3/(x+2)\) | \(-3\) |
| \(-3x/(3-2x)\) | \(9\) |
| \(-x-2\) | \(1\) |

Thus the original square identity requires the constant
\(\delta K\) to be a square in \(\mathbb Q(z)\), hence in
\(\mathbb Q\). For \(K=-3\) it is negative, and for
\(K\in\{1,9\}\) it is a nonsquare because \(\delta\) is.
This excludes every bidegree-(2,2) case, even without deciding
which of these rational degree-four covers has rational points.
It does not exclude higher bidegrees, rational constant-fibre
solutions, or any particular actual numerical PointPair.

Replay the eight interpolation cases and all four coefficient
identities with the Python standard library:

~~~sh
sha256sum -c SHA256SUMS
python3 -B replay_bidegree_22.py | cmp - EXACT-MOBIUS-CANDIDATES.json
~~~
