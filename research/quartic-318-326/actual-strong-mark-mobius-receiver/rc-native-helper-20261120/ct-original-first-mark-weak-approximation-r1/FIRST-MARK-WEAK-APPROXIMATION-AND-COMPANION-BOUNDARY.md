# One original marked point by explicit twist selection, and the exact companion boundary

Fix one literal original Ready pole, its positive squarefree
\(\beta=[17b]>1\) and \(\theta=[1-b/17]\), and an existing common selected
seed \(n_*,n_*\theta\) from the original local construction. In
particular the first seed has locally admissible \((\beta,1)\), in
ordered coordinates \((x+3d,x-d)\), and is positive, squarefree,
\(11\bmod12\), prime to \(6\theta\).
Readiness gives \(\theta>0\) square locally at \(2,3,17\) and
the two mutual support conditions
\[
       (\theta/p)=+1\ (p\mid\beta),\qquad (\beta/p)=+1\ (p\mid\theta),
       \qquad \gcd(\beta,\theta)=1 .
\]
Only the **local** conditions on the old seed are used below.
No October 2-converse, analytic-rank input, or native Lean build
enters this result.

There are infinitely many positive squarefree new twists \(n\equiv
11\bmod12\), prime to \(6\theta\), with a rational nontorsion point
of exactly the marked class \((\beta,1)\) on \(E_n\). These \(n\) may
be required to have the old \(n_*\) squareclass at any specified
finite list of places (in particular every old helper and \(q_0\)).
On their same companions \(E_{n\theta}\) the class \((\beta,1)\)
is everywhere locally admissible. This does not assert either
full Selmer size eight for the new twists, a rational companion
point, or a completed PointPair. In this precise one-parameter
construction, when \(\theta\ne1\) there is additionally an exact
obstruction to obtaining the companion by a rational-function
section over the same parameter.

## 1. Complete easy chart for the first marked point

For \(t\in\mathbb Q\), put
\[
 \begin{gathered}
  u=\beta t^2,\quad A=1+3u,\quad B=4\beta t,\quad C=2(1-3u),\\
  D(t)=\beta(1-u)(1-9u)=\beta A^2-B^2,\qquad
  X=\beta A^2,\qquad Y=\beta ABC .
 \end{gathered}
\]
Then
\[
 X-D(t)=B^2,\qquad X+3D(t)=\beta C^2,\qquad
 Y^2=X(X-D(t))(X+3D(t)).
\]
Away from the finite zero factors, \((X,Y)\) is the literal marked
point. If \(D(t)>0\), scale \(D(t)=n h^2\) with \(n\) positive
squarefree and \(h\in\mathbb Q^\times\); divide \(X,Y\) by \(h^2,h^3\),
respectively. The two squareclasses do not change.

Conversely, over \(\mathbb Q\) or any of its completions, let a
nonexceptional marked point on \(E_d\) be written
\(x=\beta a^2,\ x-d=b_0^2,\ x+3d=\beta c^2\).
The first equality follows from the product of the three Kummer
coordinates being 1. Then
\[
           \beta(2a-c)(2a+c)=3b_0^2 .
\]
Since \(b_0\ne0\), \(z=2a+c\ne0\).
With \(t=b_0/(\beta z)\) we have
\(4a/z=1+3\beta t^2\), so \(16d/z^2=D(t)\).
Thus the chart parametrizes **all the local twist squareclasses**
that have the specified nonexceptional full mark.
It is not a characterization of the weaker first-coordinate-only
PointPair contract.

At an old finite local place the Kummer coset given by the seed is
nonempty and open: multiplication by 2 on the smooth curve has
invertible derivative over the characteristic-zero local field,
and its image contains a neighbourhood of the origin. Each such
coset has points outside the finite root and origin set; hence there
is a finite \(t_p\) with \([D(t_p)]=[n_*]\) locally. The same equality
holds in a whole local ball about \(t_p\), by continuity and
openness of squares in \(\mathbb Q_p^\times\).

## 2. Weak approximation proves infinitely many first points with same old local rows

Include \(2,3\), the supports of \(n_*,\theta\), and any further
fixed finite primes among these local balls. At the real place take
a bounded open interval of small nonzero \(t\) with \(D(t)>0\) and
all three point factors nonzero. This is consistent with the positive
old real twist class. To guarantee a new global squareclass, select
a fresh odd \(p\nmid 6\beta\theta n_*\), outside all previous
squarefree parameters in this induction, splitting in
\(\mathbb Q(\sqrt\beta)\). Such primes exist by Dirichlet in a
fixed splitting progression. The polynomial \(1-\beta t^2\)
has a simple unit root modulo \(p\), and \(1-9\beta t^2\equiv-8\)
there. Take an exact residue mod \(p^2\) deepening the first factor
to valuation **one**, not two. This is one further nonempty open
ball. Ordinary weak approximation in the rational \(t\)-line
gives a solution of the simultaneous real and finite conditions.

The resulting squarefree \(n\) has \(p\) in its support, and thus
differs from every previous output. It has \(n/n_*\) a local
square at all the old places. In particular the two exceptional
places give odd \(n\) in the same residue class mod 4, \(n\equiv
n_*\bmod3\), and \(n\equiv11\bmod12\); no prime of \(\theta\)
occurs in \(n\). The \((X,Y)\) above gives an actual first marked
point with nonzero ordinate. It is nontorsion: after untwisting
over \(\mathbb Q(\sqrt n)\), the base \(E_1\) has good reduction
at 5 and 7 with respective orders \(8,8\) in degree one and \(32,64\)
in degree two (direct count or the trace formula). Using the
prime-to-residue-characteristic torsion injections at 5 and 7
excludes all odd torsion, even if a place of the quadratic field is
ramified. A rational half of the 2-torsion at \(x=0,-3n\) would
require a negative root difference to be a square, and at \(x=n\)
would require \(n\) to be square. The usual full split-root
[halving criterion](https://pure.mpg.de/rest/items/item_3117847_2/component/file_3276671/content)
therefore excludes order 4. The point with nonzero ordinate
cannot be 2-torsion.

On \(E_{n\theta}\), the same marked squareclasses are locally
admitted:
- At \(2,3\) and each \(p\mid\beta\), \(\theta\) is a local square
  by Readiness, so this is the actual local isomorphism with \(E_n\).
  The same holds over \(\mathbb R\) since \(\theta>0\).
- At \(p\mid\theta\) the \(\beta\) class is a local square by the
  reverse mutual condition, so the mark is trivial locally.
- At any other odd \(p\mid n\), the rational point on \(E_n\) already
  implies \((\beta/p)=+1\). Indeed \(\beta\) is a unit here, and the
  torsion Kummer valuation pairs \((1,1),(1,0)\) identify the full
  local image of size four; the only unit/unit image is trivial.
- At all remaining good odd primes the pair is unit/unit, hence
  in the entire unramified (good reduction) Kummer image.

Thus the construction supplies one true marked rational point and
one true marked companion Selmer class on the same two twists.
These are **not** guaranteed to be outputs of the preceding
Selmer-eight selector. Matching the old finite local classes gives
only the pooled old product symbols, not the individual Legendre
rows of any new factors or their internal graph. In fact the direct
first-point values involve *two* irreducible binary real norm forms
\(v^2-\beta u^2,\ v^2-9\beta u^2\) on the same rational inputs:
one cannot invoke a theorem on independent affine linear forms
for their simultaneous prime values. This is a precise unproved
seam if one wants to combine this construction with the two
original cardinality-eights.

## 3. Why the identical parameter cannot give a generic companion section

For any fixed \(\beta>0\), consider the smooth projective genus-one
curve \(C_\beta:w^2=D(t)\). The four branch points are simple and
distinct, so it is geometrically integral; no rational origin on
\(C_\beta\) is assumed. The first point above, untwisted by \(w\),
gives a **nonconstant** map \(C_\beta\longrightarrow E_1\) with
first coordinate \(X/D(t)\). Hence the Jacobian of \(C_\beta\) is
\(\mathbb Q\)-isogenous to \(E_1\).

If \(\theta\ne1\) is squarefree, the non-CM elliptic curve \(E_1\)
is not \(\mathbb Q\)-isogenous to \(E_\theta\).
Indeed \(j(E_1)=35152/9\) is nonintegral, and CM \(j\)-invariants
are algebraic integers. Over \(\overline{\mathbb Q}\) the Hom group
between a curve and this twist is generated by their twist
isomorphism, since the geometric endomorphism ring is \(\mathbb Z\).
The nontrivial twist automorphism negates this generator, so the
rational Hom group is zero.

A point of \(E_{\theta D(t)}(\mathbb Q(t))\) would untwist to a map
\(C_\beta\longrightarrow E_\theta\) anti-invariant under the deck
involution \(w\mapsto-w\). Any nonconstant such map would give a
nonzero Hom on the Jacobian, impossible by the preceding paragraph.
A constant map is rational (the function field is geometrically
integral), and anti-invariance then makes it a point of order
dividing 2. Thus the **entire** generic companion group consists
only of its rational 2-torsion. This excludes a universal rational
formula on this exact \(t\)-line. It does not exclude specialization
rank jumps, a different branched parameter, or any particular
rational PointPair at this pole. For \(\theta=1\) the two curves
coincide and the constructed point serves both.

Equivalently, to produce a full-marked companion inside the
explicit first-mark family without an external rank theorem,
one still needs actual rational \(t,t'\) with
\[
                  [D(t')]=\theta[D(t)]
\]
and nonzero point coordinates, with whatever old local rows are
required. This is not supplied by the weak approximation argument.

### Exact control (not an original numerical pole)

For the previously used arithmetic toy \(\beta=17,\theta=13,n_*=323\),
the test \(t=1485\) gives
\(D(t)=32^2\cdot323\cdot2635933\cdot246637\).
The replay verifies the rational first point and its exact mark,
and the same squareclasses as \(323\) at \(2,3,13,17,19\).
It does not compute a rational companion point or a Selmer size.

    python3 -B replay_first_mark.py | cmp - EXACT-FIRST-MARK-LOCAL-CONTROL.json
    sha256sum -c SHA256SUMS
