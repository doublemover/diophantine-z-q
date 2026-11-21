# Both literal original forward projections, conditional on one pointwise rank theorem

## Precise statement and what is external

Let \(P_{318}\) be the integer polynomial
Current318FinalPolynomial.P and \(P_{326}\) the literal stored
Current326CoefficientBinding.tablePolynomial (the 3157-term coefficient
table, not a newly chosen polynomial). Let the **rank input** be only
the following implication:

> If a smooth elliptic curve \(E/\mathbb Q\) has a nonzero rational
> point of order two and its full \(2^\infty\)-Selmer corank is one,
> then \(\operatorname{rank} E(\mathbb Q)=1\).

This is the rank-one part of Theorem 1.1 of the
[version-pinned 7 October 2026 OpenAI pointwise 2-converse preprint](https://github.com/openai/math/blob/4eaee87548250b2682affda7d05d947c05554bae/preprints/A-pointwise-2-converse-for-elliptic-curves-with-rational-two-torsion-October-7-2026/build/sections/introduction.tex#L12-L42).
We do not independently validate that theorem here. Neither an
analytic rank claim for the selected curves, nor finiteness of their
whole Sha as an additional premise, is substituted for it.

**Conditional forward conclusion.** For every \(a\in\mathbb Z\) there
are \(w_{318}\in\mathbb Q^{317}\), \(w_{326}\in\mathbb Q^{325}\) with
\[
 P_{318}(a,w_{318})=0,\qquad P_{326}(a,w_{326})=0.
\]
The input \(a\) is unrestricted, including zero and minus one.
There is one actual original row-assignment behind these projections.
The different witness vectors need not have identical tails.
This is a paper implication, not a Lean build, displayed numerical
solution, or the reverse exclusion of nonintegers.

Besides the indicated rank implication, the argument uses published
ordinary results (affine-linear prime patterns in finite Galois
classes, class field theory, Dirichlet, full rational 2-descent,
Cassels–Tate duality, and Legendre's ternary theorem), the independently
checked linear-denominator-prime argument, and the exact retained
original source calculations and compiler identities. The term
“one rank input” does not mean that no established analytic or
arithmetic theorem is used, or that those source calculations are
all natively checked as one packet.

## 1. One original integer and one original forward index

Apply the exact AllScalarDetectorJoin318.integer_preparation with
\((A,B,N,M)=(0,0,2^{16},1)\) to that integer \(a\). It yields \(J>0\).
Use the \(d=1\) member of the preparation: let the single label tuple
\(n_s\) be FixedArithmeticLabels318.labels at the multiplier
PreparedAnchorLabels318.multiplier \(2^{16}\,(J\cdot 1)\).
It is the original tuple, with first member \(3723(2a+1)^2\),
second member greater than 1, and the same positive odd Lucas pair.
The construction gives \(h_0\bmod L\), \(64\mid h_0,L\), retaining
the actual scalar preparation and the three original small-place
detector thresholds. The clearing \(D\), root scales and local
guards are fixed from the same labels, before choosing any contact
prime.

Use the checked linear-q paper, SHA-256
29e5419420d73d1699801548e411527e265378ebd22bde95d7f7653d59fbc3e0,
with this precise preparation. Its unconditional prime part uses
[Frei–Tinková v3, Theorem 1.4](https://arxiv.org/html/2408.17441v3#S1.SS2)
with fixed thresholds, then the independent ambient four-variable
upper bound, not a conjecture about quadratic prime tuples.
It produces \(t=u/(D^2Q^2q)\) sufficiently large and genuine
Gaussian witnesses for all selected primes. The same real CRT
theorem produces one original \(h>1\), in the original class
\(h_0\bmod L\), with the required nonzero guards, scalar norm
margin, and original source rows. The three stored detector
poles are pre 190, pre 241, pre 292 in
\[
 \mathrm{pre}=\mathrm{ThreeDetectorUniformFamily318.witness}
                 \ (a:\mathbb Q)\ n_s\ h\ t .
\]
The \(q\)-valuation is \(+1\) at each detector, with the \(q\) order
included in both LCMs but \(q\) absent from the contact \(\Pi^3\).
The exact checked folded trace, square-denominator and \(2,3,17\)
transfer give the three Ready predicates on these same \(b\)'s.
The scalar preparation retained via \(h\bmod L\), and the same
real norm margin, give Ready on the literal scalarB \(a,n_s,h\)
via the original scalarReady lemma.

The analytic cold audit is
COLD-LINEAR-PRIME-KEY-AND-READY.md,
3cd4198d2fcadc4f72956c9ede7c95a54c16867dbc729f5f4a7b1ab88944dca2;
the independent local Padé, CRT, and arbitrary-\(t\) interface
audit is INDEPENDENT-LINEAR-Q-LOCAL-AND-SOURCE-REVIEW.md,
2e984265c466c85b04098a3811defcba1892a8a8174aa88e7c5d5fffe1b164cf.
What transfers is the original source data and Ready, not an
inhabitant of the old square-contact Pattern. In particular
we do not invoke OriginalJoinedPrimeSource318.current_source
by filling that obsolete Pattern argument with a linear tuple.
We go directly to the original complete_at_index consumer.

## 2. From each same literal Ready pole to the pair of marked twists

Let \(b\) be one of those four exact rational poles. Its Ready
conditions give \(0<b<17\), square reduced denominator, and a
square with minimum depths \(3,1,2\) at \(2,3,17\).
For clarity, the original eligibility argument can be read
directly on its reduced fraction. Write \(b=b_{\rm num}/d^2\),
\(d>0\). Its positive 17-depth gives
\(b_{\rm num}=17X\); put \(Y=d^2-X>0\).
Coprimality of \(b_{\rm num}\) and \(d\) implies
\(\gcd(X,Y)=1\). Factor \(X=\beta c_0^2,Y=\theta e_0^2\) into
positive squarefree parts. At 2 and 3 the valuation of \(X\)
is positive even and division by 17 has unit class 17; at 17
it is positive odd (the valuation of \(b\) is at least two and even).
Thus the unit classes of \(\beta\) at 2 and 3 are those of
17, giving \(\beta\equiv17\bmod24\) and \(17\mid\beta\).
Also \(Y/d^2=1-b/17\) is a square unit at \(2,3,17\):
at 2 it is \(1\bmod 8\), and at 3 and 17 it is \(1\bmod p\).
In particular \(\theta\equiv1\bmod24\), with \(17\nmid\theta\).
From
\[
 \beta c_0^2+\theta e_0^2=d^2
\]
each \(\theta\) is a square unit modulo a prime dividing \(\beta\),
and each \(\beta\) a square unit modulo a prime dividing \(\theta\).
Here the other coordinate coefficient and the involved square
root are units by coprimality. These are the two required
**whole-product** signs; no assumption is made about each
individual cross symbol.
Set \(c=17c_0/d,\ e=e_0/d\). Then
\[
 17b=\beta c^2,\qquad 1-b/17=\theta e^2,\qquad c,e\ne0 .
\]
This is the exact OriginalReadyChart318.eligibility data.
The branch \(\theta=1\) is legitimate.

For this same \(\beta,\theta\) use the established original
simultaneous finite prime construction, as in
ActualTwoDescentOriginalAllPlacesCardinality318.
actual_simultaneous_all_places_eight. It chooses one squarefree
positive product \(n\), and the extended product is \(n\theta\),
with the same auxiliary primes, original \(\beta\), and a fresh
\(q_0\) dividing both products but not \(\beta\).
The theorem gives actual all-place intersection cardinal eight
and the marked class on each literal
\[
 E_\ell:y^2=x(x-\ell)(x+3\ell),\qquad \ell=n,\ n\theta .
\]
Both products are \(11\bmod12\) as required by the original finite
selector; the curve roots are distinct because \(\ell>0\).
The genuine cohomological Selmer cardinal is eight by
ActualTwoDescentActualSelmerCardinality318.actual_selmer_eight,
not by using the size of a signed proxy as if it were cohomology.
The class is \((\beta,1)\) in the \((x+3\ell,x-\ell)\)
Kummer convention.
We use the original arbitrary-support construction, so this
implication does not depend on optimizing the number of auxiliary
primes for the linear-q detector factors. Nor does it require
one simultaneous prime tuple for all four poles. For each pole
its **two** curves use one tuple. For the completed original
source the four PointPairs may be chosen independently.

## 3. Full \(2^\infty\)-corank one, without finiteness of Sha

We give a direct classical Cassels–Tate argument for each actual \(E_\ell\).
Let \(r=\operatorname{rank}E_\ell(\mathbb Q)\).
The rational two-torsion has dimension 2, with all three nonzero
points at the displayed roots. The ordinary exact Kummer sequence is
\[
 0\longrightarrow E_\ell(\mathbb Q)/2E_\ell(\mathbb Q)
 \longrightarrow\mathrm{Sel}_2(E_\ell)
 \longrightarrow\Sha(E_\ell)[2]\longrightarrow 0 .
\]
Thus \(3=2+r+\dim_{\mathbb F_2}\Sha(E_\ell)[2]\).
Write the cofinitely generated \(2\)-primary Sha as a divisible part
of corank \(d_2\) and its finite reduced quotient \(F_2\).
The structure statement follows from cofiniteness of the
\(2^\infty\)-Selmer group; the divisible part splits as an abelian
group. Only \(F_2\) is asserted finite, not the whole Sha.
The ordinary primary Kummer sequence gives
\(s_2=\operatorname{corank}_{\mathbb Z_2}\mathrm{Sel}_{2^\infty}
=r+d_2\).

For elliptic curves the classical Cassels–Tate form is alternating
and becomes nondegenerate after dividing by the maximal divisible
subgroup; see [Poonen–Stoll, introduction and Theorem 5](https://math.mit.edu/~poonen/papers/sha.pdf).
Different primary parts are orthogonal, so the restriction to
\(F_2\) is perfect and alternating. A finite abelian 2-group
with such a pairing has \(\dim F_2[2]\) even: an element of
maximum order has a partner of the same order pairing with it
to a primitive value, their perfect two-generator subgroup splits,
and induction gives pairs of cyclic summands. Consequently
\[
 1=s_2+\dim_{\mathbb F_2}F_2[2]
\]
forces \(s_2=1\). This is the **full** primary corank; a finite
2-descent excess alone, minus analytic sign alone, or ordinary
rank parity is not being substituted for it. The calculation
does not exclude \(r=0,d_2=1\) without the stated rank input.

## 4. Exact marked rational points and the two source equations

Apply the indicated rank hypothesis to the actual \(E_n\) and
\(E_{n\theta}\). They each have nonzero rational two-torsion and
the proved full corank one, hence rational rank one under that
hypothesis. Their rational Kummer groups now have order eight
and therefore exhaust their respective finite Selmer groups.
Thus \((\beta,1)\) has a rational representative on each exact
curve. The two rational torsion classes are independent:
in the \((x+3\ell,x-\ell)\) convention they are
\((\ell,1),(3,-\ell)\); the first is nontrivial because \(q_0\mid\ell\),
and the second has negative second class. The fresh \(q_0\) is not in
\(\beta\), so the mark is not among the four images of \(E_\ell[2]\).
In particular no root point or origin is a representative.
If \(x+3\ell=\beta u^2,\ x-\ell=v^2\), the selected \(u,v,y\)
are nonzero, and the literal cubic gives \(x=\beta r^2\) with
\(r=y/(\beta uv)\ne0\). These are the two exact affine
abscissas, not unmarked positive-rank points.

Let the rational ordinates of the two points be \(Y_1,Y_2\),
and their square-root abscissas \(r_1,r_2\).
Put \(B=17b\), \(d_V=B e\) and \(V=B^2(1-b/17)=\theta d_V^2\).
Scale the first curve point by \((\lambda^2,\lambda^3)\) and the
second by \(((\lambda d_V)^2,(\lambda d_V)^3)\), where
\(\lambda=c/r_1\). The output on the literal PointPair ABI has
\[
 T=n\lambda^2,\qquad s=d_Vr_2/r_1,\qquad
 y_1=\lambda^3Y_1,\quad y_2=(\lambda d_V)^3Y_2.
\]
The first new abscissa is \(B\), the second \(B s^2\);
the second curve parameter is
\(n\theta(\lambda d_V)^2=T V\). This is precisely both
NormalizedPolePoints318.PointPair equations with \(s\ne0\).
When \(\theta=1\) the same rational point can be reused.
Neither \(b\) nor \(h\), \(t\), or the original labels is changed.

## 5. Row 287 on the identical labels and scale

This is separate classical arithmetic, not a third rank input.
With the exact labels \(n_s\) chosen in §1 and \(N=2^{16}\), set
\(S=3^{2^{16}}\),
\(A=\mathrm{FixedDetectorScales318.normProduct}(n_s)\) and
\(C=\mathrm{ActualScalarRoot318.inverseNorm}(n_s(1))\).
The exact prepared anchor ratio is
\(r_0=4096A+C/S\). The original prepared-anchor depth theorem
gives \(r_0\ne0,v_2(r_0)=0,v_3(r_0)\ge0\) for these labels
with the exact multiplier \(J\cdot1\ne0\).
Write \(r_0=u_0/v_0\) reduced, \(v_0>0\).
Both \(u_0,v_0\) are odd and \(3\nmid v_0\), so
\(M_0=3u_0^2-2v_0^2\equiv1\bmod24\), in particular nonzero.

Here is the ordinary two-conic producer for this exact value.
Write \(M_0=m k^2\) with signed squarefree \(m\equiv1\bmod24\)
and \(k\ne0\), \(d_0=k/v_0\). For \(m=1\) the required affine
representation of \(3r_0^2-2\) is \((d_0,0,0)\).
Otherwise choose a prime \(p\equiv1\bmod24\),
\(p\equiv2\bmod|m|\) by Dirichlet. These congruences are reduced.
Legendre's ternary criterion gives the two conics
\[
 x^2+6y^2=p,\qquad p s^2=2z^2+m T_0^2 .
\]
For the first, \(p\) is square modulo 6 and \(-6\) square modulo \(p\);
positive definiteness supplies the nonzero denominator when
normalizing the homogeneous triple. For the second,
the modulus-\(|m|\) square is \(2p\equiv4\), the modulus-2
condition is automatic, and
\[
 (-2m/p)=(m/p)=(2/|m|)=+1
\]
by reciprocity, \(p\equiv1\bmod24\), and \(|m|\equiv1\) or \(7\bmod8\).
This also covers signed negative \(m\), without individually
requiring its prime factors to be squares of 2. The coefficients
are pairwise coprime signed squarefree. A nonzero second solution
must have \(T_0\ne0\): otherwise \(p s^2=2z^2\) forces both zero
by the \(p\)-valuation. Thus
\[
 (X_0,Y_0,Z_0)=\frac{d_0}{T_0}(xs,ys,z)
\]
gives \(X_0^2+6Y_0^2-2Z_0^2=3r_0^2-2\).
Scaling all three by \(S\) is the **actual** row-287 equation
\[
 X^2+6Y^2-2Z^2=3(4096AS+C)^2-2S^2 .
\]
It produces ScalarCompleteSource318.Anchor \(S,A,C\).
This is the same arithmetic as ActualPreparedAnchor318.current
with these exact prepared labels; it does not ask for a different
\(J\), extra chosen slope or a reselected \(h\). Under the
literal consumer \(A\) is the existing slot 145 and \(C\) the
existing selected scalar root in slot 308. Slots 55,56,57 use
the three affine coordinates of this anchor. The proof uses
ordinary Legendre ternary and Dirichlet, not an unsupported
rank-four local-global theorem. See the exact independent
ACTUAL-287.md, 7d3421f0385a0e67b254fdf0cdc46ee86a58a3a13665e05d32b8f3ea1ddf437c.

## 6. One raw source solution, both original exact tables

Pass the same \(a,n_s,h,t\), original nonzero real guards and scalar
norm margin, actual detector pre-rows, four original PointPairs and
this anchor to PreparedIntegerSource318.complete_at_index.
Its pre-pole and scalar fillers put the certificates into the same
raw source at scale \(S\); the preserved slots match the scalar
pole and anchor to the same labels. This gives
\[
 \mathrm{HasSolution}\bigl(\mathrm{Raw318FinalReplay.stage0}(S)\bigr)
                         (a:\mathbb Q).
\]
The exact polynomial interfaces then take this exact same source
proposition in the forward direction:
Current318FinalBridge.polynomial_zero_iff_source and
Current326Final.table_zero_iff_source. The latter includes the
actual stored-table equality, not just a structurally similar
SOS equation. The two conclusions are the displayed forward
projections at 318 and 326. They do not establish the distinct
rational reverse arithmetic, which would need
source-solubility \(\Rightarrow\) integrality for **all** rational
inputs. Do not infer this from the table equivalences.

### Selected exact immutable source pins

| Source | SHA-256 prefix | Role |
|---|---|---|
| AllScalarDetectorJoin318 | 36f345e2 | one original preparation and \(J\) |
| OriginalJoinedPrimeSource318 | a0adb7ca | actual Ready/old Pattern boundary |
| OriginalReadyChart318 | 98faa96a | precise per-pole eligibility |
| ActualTwoDescentOriginalAllPlacesCardinality318 | d8190dcd | same tuple, both genuine all-place sizes |
| ActualTwoDescentActualSelmerCardinality318 | 1fe1139f | cohomological \(\mathrm{Sel}_2\) coercion |
| ActualPreparedAnchor318 | 71e234f1 | original row 287 and same scale |
| NormalizedPolePoints318 | 410995ba | actual two equation contract |
| PreparedIntegerSource318 | e3ecec83 | end-to-end raw source consumer |
| Current318FinalPolynomial | ad54e02e | actual \(3^{2^{16}}\) scale and literal \(P\) |
| Current318FinalBridge | e8e1185e | 318 exact projection |
| Current326Final | c15dec46 | 326 exact projection |
| Current326CoefficientBinding | 47a80553 | actual integer coefficient table |

This is intentionally an **all-integer forward paper integration
conditional on the precise stated rank implication**. No evaluation
of a final coefficient vector, native theorem selection/export,
or unconditional source/projection theorem is claimed.
