# Actual alternate support: exact finite scan, CM height barrier, and matrix rank

Retain exactly the materialized original scalar \(c=C/Z=12W/(1+A)\)
of the published fixed-\(h,J\) calculation, in lowest terms.
Write \(D=\beta c^2\), \(H=Z^2-\beta C^2\), and
\(L'=49\beta C^2-48Z^2\) for the alternate cover's data;
this \(H\) is not the original source chart norm.
Use the full local criterion of e6778189. Its new prime rows
are primes of \(C\) with \((3\beta/p)=1\) and primes of \(L'\)
that are split or of odd depth. Every latter prime outside the
fixed places also necessarily has \((3\beta/p)=1\), by
\(\beta c^2\equiv48/49\bmod p\).

This note proves a stronger absolute lower bound for the
untracked odd-denominator factors. It checks the complete
new-support locus below 20 million and the first-rank-dependent
sub-locus below 120 million. It does **not** compute a reduced
denominator character, determine all prime support, or supply a
locally admissible or rational point for the full scalar.

## Formal recovery across an actual source chart zero

The literal source is \(E:y^2=x^3-d^2x\) over \(\mathbb Q(\sqrt2)\),
with \(d=3-\sqrt2\), \(R_0=(1+\sqrt2,2\sqrt2)\),
\(U(P)=2y/(x^2+d^2)\), and \(x([2]P)=U(P)^{-2}\).
The fixed scalar uses \(U_h=U([h]R_0)\) and
\(U_i=U([i]R_0)\) with \(i=6^{15}3^{65536}J=mh\).
In particular \(v_2(h)=6\), \(v_2(i)=22\), and \(m\) is even.
For efficient modular evaluation the exact equality
\[
 m=6^{15}3^{65532}\bigl(J/\gcd(h,J)\bigr)
\]
follows from \(h/\gcd(h,J)=81\), independently checked in the
matrix script. No expanded elliptic coordinate is used.

At a good source odd place, whenever \(U_h\) has zero residue
the point \([h]R_0\) reduces to a 2-torsion point \(T\)
(including \(O\)) and \([i]R_0\) reduces to \(O\).
With the formal parameter \(z=-x/y\) at \(O\),
\[
 \frac{U_h}{z([2h]R_0)}
 \equiv
 \begin{cases}
 -1,&T=O\ \text{or}\ T=(0,0),\\
 +1,&T=(d,0)\ \text{or}\ T=(-d,0).
 \end{cases}
\]
At \(O\), \(U=-2z+O(z^2)\) and \(z([2]P)=2z+O(z^2)\).
At affine \(T\), use the exact doubling slope
\(\ell=(3x^2-d^2)/(2y)\) and
\(y_2=\ell(x-x_2)-y\). The reduction of
\(-U_h y_2/x_2\) is precisely the reduction of
\(U_h\ell=(3x^2-d^2)/(x^2+d^2)\). The discarded
terms vanish since \(x_2^{-1}\) is positive depth
and \(x,y,U_h\) are integral there. The formal law
\(z([m]Q)/z(Q)\equiv m\bmod p\), valid also when
\(p\mid m\), and the reduction of \([i]R_0\) at \(O\)
give the exact integral ratio
\[
  U_i/U_h\equiv m\pmod p \quad(T=O,(0,0)),\qquad
  U_i/U_h\equiv -m\pmod p \quad(T=(\pm d,0)).
\]
The stable scalar factor is \(Q=\mathrm{Norm}(U_i/U_h)/R^{15}\),
\(R=4376874610839020\), not a division of zero residues.
Separate prime-square controls verify actual split \(O\) at
23, actual split nontrivial \(T_\pm\) at 1279, and actual
inert \(O\) at 19, plus a nonactual \(T_0\) orientation control
at 23. The row labels in the JSON explicitly separate this canary.

## Stronger crossed-pole lower bound from the actual CM action

At a split good source prime \(p\) in \(\mathbb Q(\sqrt2)\),
a pole in \(U([j]R_0)\) means that its reduction has exact
order 4, since its doubled abscissa reduces to zero at the
nontrivial 2-torsion point. Equivalently the residue point is
affine with \(x^2=-d^2\), \(y\ne0\); in particular \(p\equiv1\bmod4\).
The \(\mathbb F_p\)-automorphism
\([{\rm i}](x,y)=(-x,\sqrt{-1}\,y)\) fixes \(O\) and squares
to \([-1]\), so the actual finite group has its
\(\mathbb Z[{\rm i}]\)-module structure.
If \(v_2(j)=a\), the order of \(R_0\) has 2-depth exactly \(a+2\),
by the elementary order of a multiple. Its 2-primary
part \(P\) has integer order \(2^{a+2}\).
The Gaussian ideal annihilating \(P\) contains \((2^{a+2})\)
and hence is \((1+{\rm i})^r\) up to unit. The integer order
is \(2^{\lceil r/2\rceil}\) by its exact intersection with
the integers. Thus \(r\ge2a+3\), and
\(\#\langle\mathbb Z[{\rm i}]P\rangle=2^r\).
Hasse gives
\[
  p\ge\lceil(\sqrt{2^{\,2a+3}}-1)^2\rceil.
\]
In particular an \(h\)-pole requires \(p\ge32407\), and an
\(i\)-pole requires \(p\ge140737464628763\). This improves
the earlier order-only lower bound, without assuming an
exact Frobenius sign or cyclic full finite group.
At inert good primes the former trace bound \(v_2\#E(\mathbb F_{p^2})\le5\)
already excludes both kinds of poles and is unaffected.

The earlier crossed-pole analysis shows that every odd extra
negative valuation of \(W\), outside the fixed normalizer
and support, requires an \(i\)-pole. Thus the squarefree
denominator is exactly
\[
 \operatorname{sf}(Z)=(1+A)\,Z_{\mathrm{exceptional}},
\]
where \(1+A=29\cdot181\cdot1346909\cdot70850399941\)
is squarefree and all four local \(W\) values are units,
and every odd prime of \(Z_{\mathrm{exceptional}}\) is at least
\(140737464628763\) and splits the four known characters
\(2,-1,7,-R\). Here the assertion about the four fixed primes,
and positivity/unit guards at the other fixed places, are
used from the checked old scalar normalizer and crossed-pole
receipts, not inferred from the new scan. Any individual
required \((Z/p)\) equals the computable fixed factor times
\((Z_{\mathrm{exceptional}}/p)\). The latter is **not**
inferred to be \(+1\) from the bound or the splitting data.

## Exact bounded support scan

The adjacent C++17 calculator is exact integer finite-field
arithmetic. Candidate annihilators are independently verified
against the actual point in every completion before using
them; failures and unresolved poles have separate counters.
It uses the formal recovery even when one or both chart
residues are zero. It asserts the CM exclusion of any \(i\)
pole in its allowed range. At a remaining source \(h\)-pole
one has positive \(i\)-depth at the same place. If both \(h\)
charts are poles, the norm \(N=\operatorname{Norm}(1+U_h^2/R)\)
has negative valuation while \(Q\) has positive valuation,
so \(W\) is a pole. If exactly one is a pole and the other
factor \(1+U_h^2/R\) is nonzero mod \(p\), the same conclusion
holds. Otherwise one would need a higher-precision
calculation and the scanner explicitly defers. In each
rigorously excluded case \(p\nmid1+A\) and \(c\) is a pole,
so the primitive \(C,H,L'\) are all units (outside the
already treated 2,3,7 and \(\beta\)).

For \(11\le p\le20\,000\,000\) all primes with the necessary
\((3\beta/p)=1\), outside fixed normalizer and bad places,
were accounted for: 634,757 relevant, 634,752 evaluated,
4,184 formal recoveries included, 5 excluded poles,
0 deferred, 0 failed annihilators. The **only** hit
is the known actual \(L'\) prime 83; there is no relevant
\(C\) prime or split/even \(L'\) prime in that range.
Special primes below 11 are already handled by 2/3,
\(5\mid\beta\), and the explicit good 7 row. Fixed normalizer
primes are denominator primes, not relevant \(C,L'\) support.

## Symbolic RHS, exact matrix kernel, and first rank-sensitive locus

The 12 known support columns are
\[
 (5,11,17,163,661,733,1489,1861,\quad131,6551,2470991,16782959).
\]
The first eight are the factors of \(\beta\); the four others
are checked valuation-one primes of \(H\). Encode Legendre
signs as bits. Include the dyadic row, row 3, all eight
\(\beta\)-rows with the correct stripped diagonal, and
the actual \(L'\)-row 83. The dyadic RHS is 1, the other rows
use the **actual** \(Z\) characters; \((7/83)=1\). The
checker tabulates all 4096 support choices and proves that
every one of the 2048 RHS vectors has exactly two lifts.
Thus the eleven rows are independent on just those columns
even before adding any unseen \(H\) factors. Both lifts
differ by the known mask product
\[
 k_0=5\cdot11\cdot163\cdot733\cdot1489\cdot6551
        \cdot2470991=158389989243518750905 .
\]
This is true for any values of the \(Z\) phases, not an
assertion that a chosen set of phases is actual. In
particular the known rows alone can never prove an
obstruction, even if all their signs were computed.

For an additional prime \(p\) giving a relevant \(C/L'\)
row, its row on these columns lies in their span exactly
when \((k_0/p)=1\). If the symbol is \(-1\), the new row
selects one of the two lifts for **every** RHS. This gives
an adaptive single-row obstruction target, not merely more
height. Scanning \(20\,000\,000<p\le120\,000\,000\) on
that dependent sub-locus accounted for 1,393,732 relevant,
1,393,730 evaluated, 1,885 formal recoveries included,
2 excluded poles, 0 deferred, 0 annihilator failures,
and no hit. No claim is made in this second range about
the complementary symbol \(-1\). Several such latter rows
could still conflict on the restricted known columns,
and any new \(H\)-columns must be accounted for before
deducing a global failure. An exact \(Z\) phase or row
dependence on this finite projection is not by itself an
all-support theorem.

## Replay

The two Python scripts use the standard library and the
unchanged scalar and inert precision helpers in the exact
sibling directories. The fixed-scalar JSON comes from its
published replay bundle. From this directory:

    sha256sum -c SHA256SUMS
    PYTHONDONTWRITEBYTECODE=1 python3 check_alt_known_matrix.py | cmp - ACTUAL-ALT-KNOWN-MATRIX.json
    PYTHONDONTWRITEBYTECODE=1 python3 check_alt_formal_ratio_controls.py | cmp - ALT-FORMAL-RATIO-CONTROLS.json
    g++ -std=c++17 -O3 find_alt_discriminant_primes.cpp -o /tmp/find_alt_discriminant_primes
    /tmp/find_alt_discriminant_primes 2000000 | cmp - SCAN-FORMAL-2M.txt
    /tmp/find_alt_discriminant_primes 20000000 2000001 | cmp - SCAN-FORMAL-20M.txt
    /tmp/find_alt_discriminant_primes 120000000 20000001 dependent | cmp - SCAN-FORMAL-DEPENDENT-120M.txt

This is finite arithmetic source, not a Lean target or
evidence of a global cover solution.
