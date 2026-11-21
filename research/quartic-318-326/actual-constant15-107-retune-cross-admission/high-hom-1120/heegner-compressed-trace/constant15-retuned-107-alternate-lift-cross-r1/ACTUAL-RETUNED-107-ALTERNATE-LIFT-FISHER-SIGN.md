# A negative cross sign on the alternate full lift at the actual 107 retune

Use exactly the [107 retune of the original \(a=0\) scalar](../../../rc-native-helper-20261120/ct-original-constant15-nonnorm-retune-107-r1/EXACT-ACTUAL-NONNORM-RETUNE-AT-107.md),
SHA-256 73fb453838ee642f97c46da6dbb1538f963da83c4908d17738ad68e0eaa1bf48.
In particular the original \(h\) and first class \(\beta=204618888056724185\) are unchanged, and \(c,\delta=1-\beta c^2,\theta=[\delta],d=\beta\theta\) are the **retuned**, not the old fixed, quantities. Its entire odd denominator squareclass is
\[
 K=1+2448\beta=29\cdot181\cdot1346909\cdot70850399941 .
\]
Its visible \(\theta\)-support is \(131,6551,2470991,16782959,107\);
the earlier four data are retained, and the literal retune has
\(c\equiv3405,\ \delta\equiv107\bmod107^2\).
The retune donor proves there is at least one further odd-support
prime. Here we compute a second cross sign **provided** the
specified alternate lift and the opposite test are truly admitted.
The exact one-further-prime hypothesis is sufficient for both.
No complete support or rational point is obtained.

## 1. Literal mark, lift, and the two rational tangent points

Keep the exact models and directions
\[
 E_d:y^2=x(x+16d)(x+25d),\quad E'_d:y^2=x(x-d)(x-81d),
 \qquad \varphi:E_d\longrightarrow E'_d,\quad \psi:E'_d\longrightarrow E_d.
\]
The marked first scalar \(\varphi\)-class is \(\theta\).
Set
\[
 e=2952271997968816765,\qquad
 f=65029284442765=5\cdot17\cdot107\cdot733\cdot1489\cdot6551 .
\]
The 107 prime simultaneously obstructs the old full lift
\((\theta,\theta,1)\) and the old opposite test \(e\).
Instead use \((\theta,\theta e,e)\) as full Kummer triple on
\(E'_d\) and \(f\) in the opposite \(\psi\)-Selmer group.
These are logically separate admissions, not assumptions built into
a computation of a local symbol.

Here is the local lift test directly. In the coordinates ordered
by \(0,d,81d\), the full Kummer of \(\varphi(P)\) equals
\((1,x(P),x(P))\): the rational \(\varphi\) x-coordinate is
\(X=x+41d+400d^2/x\), and \(X-d=(x+20d)^2/x\),
\(X-81d=(x-20d)^2/x\). This extends to torsion by the same
Kummer map. At a \(\theta\)-prime \(p\), \(d\) and \(\theta\)
have the same odd-depth class because \(\beta\) is square there.
The torsion class at \(81d\) gives the triple \((d,5d,5)\).
Thus the alternate lift is local iff \(e/5\) belongs to the
opposite scalar local image \(\{1,-d\}\). At the four old
\(\theta\)-primes \((5/p)=+1\) and the old known \(e\) meets
the local scalar test. At 107 and all further primes \(e/5\)
is a unit, so the criterion is \((5e/p)=+1\).
At 107 both \(5\) and \(e\) are nonsquares so this passes.
At \(\beta\)-primes, 2, and 3 the first class \(\theta\) is
square and the stated local \(\psi\) table admits \(e\); this
is exactly the old visible test, unchanged. At infinity all
entries are positive, and at a good odd place outside \(d\)
the four unit triples of product square are the full local
2-Kummer image (the four classes of a good rational-full-2
cubic at odd residue characteristic).

The optional no-count version of the result assumes
\((5e/p)=+1\) for all further \(\theta\)-primes, and
\(f\in\operatorname{Sel}^{(\psi)}\) at the actual retune.
The retune donor verifies all fixed \(f\)-rows. Thus its
additional \(f\)-conditions are \((f/p)=+1\) at all further
\(\theta\)-primes, because \(f\) is a unit there and the
opposite local image is \(\{1,-d\}\). These are genuine
conditions at unseen places, not inferred from aggregate bits.

Use the square-equivalent coefficient \(d_{\rm raw}=\beta\delta\)
and represent the lift by the intersection
\[
 C':\qquad X^2-eY^2=\beta T^2,\qquad
                  X^2-81\beta T^2=e\delta Z^2 .
\]
The original coordinates on \(E'_{d_{\rm raw}}\) are
\(x=\delta X^2/T^2,\ y=e\delta^2XYZ/T^3\), verifying the
literal ordered full triple \((\delta,\delta e,e)\).
Use the fixed norm identity from the
[fixed-field Artin packet](../actual-zero-ordinate-fixed-artin-reciprocity-r1/FIXED-ARTIN-RECIPROCITY-FOR-THE-LITERAL-CROSSED-SIGNS.md),
\[
 a=31859917667562016618135,\quad b=59323292900802,\quad
 z=9995282212057,\qquad a^2-\beta b^2=e z^2 .
\]
It gives a rational point \((a,z,b)\) on the first conic,
and multiplication by \(1+c\sqrt\beta\) gives the second
point \((a+\beta cb,(b+ca)/9,z)\), ordered by \(X,T,Z\).
The exact tangents are
\[
 L_1=aX-ezY-\beta bT,\qquad
 L_2=(a+\beta cb)X-9\beta(b+ca)T-e\delta zZ .
\]

The form \(L_1 L_2/T^2\) is a pushout function for \(T_0\)
on the Jacobian \(E'_d\), as in
[Fisher, §3 and Theorem 2.1](https://arxiv.org/pdf/1509.03234).
Indeed each tangent pulls back to twice a fibre of the
corresponding degree-two conic projection. Over an algebraic
closure choose those two fibres to share one of the four
\(T=0\) points. They then contain one separate sign flip in
\(Y\) and \(Z\), respectively. Subtracting the hyperplane
fibre \(T=0\) leaves the difference of the initial point and
the one with **both** flips, the translation by \(T_0\) in
the usual split full-Kummer coordinates. A fibre class does
not depend on the chosen conic basepoint; this proves the
orientation also for the two displayed rational tangents,
which need not share an infinity point.
The Hilbert evaluation can use \(L_1L_2\), omitting the square
\(T^2\) and taking a nearby admissible point when a denominator
vanishes. In this unaugmented case the first \(\psi\) form is
zero, so an admitted \(f\) is in the required second domain.

## 2. All finite nontrivial candidate places have explicit signs

At the real place \(f>0\); at 3 \(f\equiv1\bmod3\); and at any
\(p\mid d\) not in the displayed support of \(f\), admission
forces the unit \(f\) to be square. All these signs are \(+\).
The remaining special places are checked as follows.

* **At \(p=5,17,1489\).** Here \(\beta,e,f\) have depth one,
  \(a\) is divisible by \(p\) from its fixed norm identity,
  \(z\) is a unit, and \(\delta\equiv1\bmod p\).
  Use \(T=1,X=0,\ Y=\sqrt{-\beta/e},\
  Z=9Y/\sqrt\delta\) with \(\sqrt\delta\equiv1\bmod p\).
  Both square roots exist since \(e\) has the old local
  class \(-d\). Choose the sign of \(Y\) so that \(L_1/p\)
  is a unit, possible because its nonzero linear coefficient
  of \(Y\) is a unit. Then \(L_2/p\equiv9L_1/p\bmod p\)
  as \(ca\equiv0\bmod p\). Thus the product has depth two
  and square stripped unit, giving \(+\).
* **At 733.** Now \(e\) is a square unit and \(\delta\equiv1\bmod p\).
  Set \(T=0,X=1,Y=\pm1/\sqrt e,Z=Y/\sqrt\delta\).
  The two tangent values agree modulo \(p\) since \(\beta\)
  vanishes, and choosing one sign makes them units. Sign \(+\).
* **At 6551.** Put \(s=\sqrt\beta\) with \(sc\equiv-1\bmod p\)
  (the retained \(c\) residue is 2194 and \(s\equiv4649\)).
  Use \(T=1,\ X=s,\ Y=0,\ Z^2=-80\beta/(e\delta)\).
  This square root exists since the old \(e\) local class
  is \(-d\) and \(5\) is square; \(v_p(Z)=-1\).
  We have \(a-sb\equiv2382\) a unit. Modulo \(p\) the
  tangents are \(s(a-sb)\) and \(10s(a-sb)\), since
  \(e\delta Z\) has depth one. Both are units and their
  product has square unit class as \((10/p)=+1\).
* **At 107.** With \(sc\equiv-1\bmod107\), \(s\equiv62\);
  choose \(T=1,\ X=9s,\ Z=0,\ Y=\pm4s\sqrt{5/e}\).
  Here \(5/e\) is square even though each factor is nonsquare.
  The exact two residues of \((L_1,L_2)\) are
  \((69,101)\) and \((25,101)\). Each product is a nonzero
  square, giving \(+\).
* **At 2.** We have \(\beta,\delta\equiv1\bmod8\),
  \(v_2(c)=2\), \(e,f\equiv5\bmod8\), \(a,z\) odd and \(b\)
  even. Take \(X=1,T=2\); both resulting square roots
  \(Y,Z\) exist, being odd units with square arguments modulo
  eight. Changing the sign of \(Y\), respectively \(Z\),
  switches the corresponding \(L_1\), respectively \(L_2\),
  between \(0\) and \(2\bmod4\); take both valuations one.
  Their product has even depth and \(f\) represents the
  unramified squareclass 5, so its Hilbert sign is \(+\).

For every other odd \(p\) with \(p\nmid 3d\), \(f\) is a unit.
Here \(\beta,e\) are units and \(\delta=\pi^{2k}\delta_1\)
has even depth (since \(p\nmid d\)); use \(Z'=\pi^k Z\).
With a primitive projective vector in the normalized four
coordinates, each conic projection is primitive: if three
of a projected triple vanish modulo \(p\), its equation and
the other conic force the omitted coordinate to vanish.
The first tangent point is already primitive (\(\gcd(a,b,z)=1\)).
For the second tangent point in the normalized conic its
three coordinates are
\[
       a+\beta cb,\quad (b+ca)/9,\quad \pi^k z .
\]
The common depth is the minimum of the depths of the first
two coordinates, since the second conic with all unit
coefficients forces the third depth to be at least that
minimum. In the split algebra these first two coordinates are
equivalent by an integral change of basis to the two arms
of \(\sigma(1+c\sqrt\beta)\), \(\sigma=a+b\sqrt\beta\).
Both arm depths of \(\sigma\) are even: at most one vanishes
and the norm has depth \(2v_p(z)\). If \(c\) is integral both
arm depths of \(1+c\sqrt\beta\) are even too (at most one
vanishes, with its depth that of \(\delta\)). If \(c\) is a
pole, both have depth \(-h\), \(h=-v_p(c)\).
In the inert algebra \(\sigma\) is a unit by primitivity
and its exact norm, and \(1+c\sqrt\beta\) is a unit when
\(c\) is integral and has depth \(-h\) otherwise.
Thus making the second tangent point primitive removes an
even scalar depth if \(c\) is integral, and a scalar depth
congruent to \(h\bmod2\) if \(c\) is a pole.

On a good unimodular conic a primitive tangent at a
primitive isotropic point evaluates to even depth at every
primitive isotropic point off the tangent: in a Witt basis
with unit hyperbolic pairing the equation is \(uv+\epsilon w^2=0\)
and the tangent is \(v\). If \(v\) is nonunit, \(u\) is a unit
and \(v\) has twice the depth of \(w\). This applies to both
normalized conics here. It follows that the only remaining
symbol at odd \(p\nmid3d\) is \((f/p)^h\) at a pole;
all other signs are \(+\). The complete odd pole product
is thus exact:
\[
 \begin{array}{c|rrrr}
 p&29&181&1346909&70850399941\\ \hline
 (f/p)&+&+&-&+
 \end{array}
\]
using the exact retune removal of every exceptional odd
denominator prime. We conclude
\[
      \boxed{\Theta_2(\theta,f)=-1\quad
        \text{whenever the stated lift and test are both admitted}.}
\]

## 3. Exact implications and limits

Under the two admission hypotheses with any further support
count, the negative sign prevents \(\theta\) from being
rational in the \(\varphi\) scalar image, by Fisher's
kernel theorem. That rejects this particular conductor-15
receiver, not the original PointPair itself or another receiver.

Under the specific conditional **one further prime beyond the
five visible \(\theta\)-primes**, the retune donor proves the
two admissions and both scalar dimensions exactly two. The
first pairings then both vanish: they are alternating and each
has its rational torsion line in the radical. The displayed
nonzero cross sign forces both next radicals to be at most
one-dimensional. Both contain their respective rational
torsion lines, so both actual rational scalar images are
exactly those lines. The dual-isogeny rank identity gives
\(\operatorname{rank}E_d(\mathbf Q)=0\) for this retune under
that support-count hypothesis, with no assumption on Sha.
No rank conclusion is asserted for larger unknown support
without additional Selmer information. In particular neither
the support-count premise nor the two no-count admissions
are proved by the finite tangent computation.

### Exact finite replay

    python3 -B check_retuned_107_alternate_cross.py | cmp - EXACT-ALTERNATE-107-CROSS.json
    sha256sum -c SHA256SUMS

The script reads the immutable actual 107 retune donor JSON
at its relative project path and validates its digest first.
