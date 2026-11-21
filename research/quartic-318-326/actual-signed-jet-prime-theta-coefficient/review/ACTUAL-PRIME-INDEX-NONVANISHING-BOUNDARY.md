# Prime-index boundary for the selected fixed-mover ramified jet

This note audits theorem applicability and gives a sufficient quantitative
target, not a nonvanishing or general impossibility theorem. Fix the actual
lower curve of level \(N=205042530\), fixed \(p_a=415721\), and the auxiliary
\(-2207\). Hold \(q_a,q_1\) fixed as in the historical same-scale selection
(70410179), and let \(q=q_2\) be the remaining actual fresh prime, with its
ordinary Cassels sign choice and all prior order/contact conditions. For
\(M=2207\cdot976393\cdot p_a q_a q_1\), the relevant fundamental norm
is \(Mq\). Write \(A(Mq)\) for the actual signed modular-differential
coefficient read modulo \(p_a\), or \(B(q)=A(Mq)\) after exact shaving
of the fixed norm factors. No unproved identification with another
modular eigenform is implicit in this notation.

## What the standard results do and do not read

* [Ono–Skinner, Theorem 1 and Corollary 4](https://arxiv.org/pdf/math/9611225):
  the principal half-integral theorem, under their goodness hypothesis,
  gives infinitely many nonzero **squarefree** coefficients for all but
  finitely many reduction primes. Their local-conditions consequence for
  complex twists also retains the almost-all-reduction-primes condition;
  it neither verifies this fixed \(p_a\) nor restricts to a single
  varying prime and the actual finite nonabelian cap. Where their proof
  uses Galois representations on an integral-weight form obtained by
  multiplying by a unary theta series, a prime-index nonzero coefficient
  of the product detects a weighted sum of coefficients of the
  half-integral form at shifted indices \(q-dm^2\). It does not
  detect the raw coefficient at \(q\).
* [Bruinier, Theorem 4](https://www.mathematik.tu-darmstadt.de/media/algebra/homepages/bruinier/publikationen/fcmodl.pdf):
  this also concludes infinitely many squarefree indices, with extra
  hypotheses of half-integral Hecke eigenform, nonzero reduction,
  reduction prime prime to level, and outside his specified exceptional
  set. The actual local jet theta construction uses a \(p_a\)-part in the
  lattice/congruence level; an identification with a form of level
  prime to \(p_a\) is not established. Even granting all those hypotheses,
  the conclusion is not prime-index nonzero under the required ray.
* [Bellaïche–Green–Soundararajan, Theorem 1 and Lemma 2](https://arxiv.org/pdf/1704.07440):
  the general nonzero-modulo-prime statement is an unfiltered count
  \(\gg\sqrt X/\log\log X\), assuming the form has nonzero reduction here.
  Their positive-density prime-multiple lemma is for **integral**
  weight; the half-integral proof again goes through a product and
  square shifts. It gives no positive lower bound on \(B(q)\) at primes
  in the required cap.
* [Chida–Wakatsuki, Theorems 1.2–1.3](https://arxiv.org/html/2310.19496):
  the prime-discriminant complex central-value results are for the
  specified level-2 weight-8 and level-6 weight-4 forms, proven using
  their mod-2 congruence argument. They are not a general theorem for
  this level/form, fixed norm times prime, and \(p_a\)-indivisibility.
  [Uniform nonvanishing, 2610.11974v1, Theorem 1.1](https://arxiv.org/html/2610.11974v1#Thmtheorem1)
  is at strict \(\Re(s)>(k+1)/2\), not at the central value and not a
  finite-field coefficient statement.
* [Burungale–Tian, Theorem 1.3 and Corollary 1.4](https://arxiv.org/pdf/1712.01465):
  the horizontal result is valuable because it can use a given infinite
  sequence of CM fields, but it proves growth in the number of qualifying
  varying class-group characters with nonzero **complex derivative**.
  It does not force the single specified genus character or residual
  first-order formal nonvanishing.
* [Kriz–Li, Theorem 2.9](https://arxiv.org/pdf/1606.03172) compares
  residual-congruent eigenforms in one CM field with their common
  split Heegner setup, not our ramified \(p_a\) and varying fields.
  Moreover no direct comparison by a quadratic self-twist of the
  actual lower residual curve is possible. Its semistability and
  \(p_a>11\) imply full \(\mathrm{GL}_2(\mathbb F_{p_a})\) image by
  [Mazur, Theorem 4](https://www.math.columbia.edu/~goldfeld/Mazur-Goldfeld1978.pdf#page=3).
  An isomorphism with a twist by a quadratic character forces that
  character trivial on the kernel (scalar \(+I\) cannot be conjugated
  to \(-I\) in odd characteristic). It would therefore factor through
  \(\mathrm{GL}_2\), hence through the determinant by perfectness of
  \(\mathrm{SL}_2\). The sole nontrivial candidate is a contradiction
  on \(\mathrm{diag}(1,u)\) with \(u\) a nonsquare not equal to \(-1\),
  because its trace is nonzero. This argument does not exclude
  congruences with other genuinely different modular forms.

## Exact algebraic distinction from good Hecke saturation

At a prime \(l\) prime to the half-integral level, the three indices in
the coefficient of \(T(l^2)\) are \(nl^2,n,n/l^2\) (with the usual
zero convention). These have the same rational squareclass. Likewise
a fixed-t Shimura lift has only input terms indexed \(tm^2\); replacing
\(m\) by an allowed prime gives no coefficient in the new fundamental
squareclass \(tq\). Thus a proved seed with norm \(M q_0\), even an
eigenvector and every good Hecke relation, does not directly propagate
to \(M q\) for another prime \(q\). A Chebotarev read on a true
integer-weight \(T(q)\) is not a read of \(A(Mq)\) absent an additional
proved coefficient identity. This does not claim that no such new
identity or modular technique can exist.

Similarly, primitive ternary representation and a nonzero individual
pair give no lower bound on the signed sum modulo \(p_a\). Its different
classes have actual signs and repeated geometric labels, and may cancel.

## A sufficient target with the actual infinite Gaussian gcd tail

Let \(G=\mathbb Q(i)\), and fix the old finite cap \(F/G\), including
all chosen squareclasses, contact primes, exact order caps and the last
Cassels governor. Let \(S\) be the rational primes already handled there.
For \(Y\ge5\), let \(C_Y(X)\) count **degree-one Gaussian prime ideals**
of norm \(q\le X\) in the exact prescribed finite cap such that

1. \(A(Mq)\ne0\bmod p_a\), and
2. no unhandled prime \(l\le Y\), \(l\equiv1\bmod4\), divides both
   actual Gaussian-neighbour group counts.

The original two-tail argument (30b5f14f, section 4) is unconditional:
for \(Y<l\le X^{1/4}\) it removes at most
\[
 32\,\frac{X}{\log X}
 \sum_{l>Y,\ l\ {\rm prime},\,l\equiv1\bmod4}\frac{1}{(l-1)^2},
\]
by the fixed-field [Gaussian ray Brun–Titchmarsh theorem](https://arxiv.org/pdf/2210.11051),
and for \(l>X^{1/4}\) the lattice estimate is \(o(X/\log X)\).
These upper bounds apply to any subset, including the nonzero
coefficients, without equidistribution in the filtered subset.
Consequently it suffices to exhibit **one fixed \(Y\)** with
\[
 \liminf_{X\to\infty}\frac{\log X}{X}C_Y(X)
 >32\sum_{l>Y,\ l\ {\rm prime},\,l\equiv1\bmod4}\frac{1}{(l-1)^2}.
\]
This yields infinitely many actual selected primes with the desired
coefficient nonzero, and the already established original common-index
CRT and local-ball constructions apply. A \(Y\)-uniform positive liminf
for all large cutoffs would suffice. Alternatively one single **exact**
allowed prime and coefficient evaluation suffices for existence without
a density theorem. Positive densities of a coefficient set and of the
old selector separately are not enough.

One possible way to prove the requisite density would be a new finite
Frobenius witness guaranteeing \(B(q)\ne0\) over the exact old cap.
Any newly ramified rational prime would first need to be admitted with
its two actual group counts units or otherwise explicitly controlled.
Then the remaining fresh Gaussian rays are disjoint by the old relative
ramification argument, the positive finite-cap density survives the
finite good ray product, and the two old tails apply with \(Y\) chosen
after that fixed density. No such coefficient Frobenius witness, nor
a numerical coefficient in the actual selected family, is supplied here.

Signed: independent reviewer, 2026-11-21 UTC.
