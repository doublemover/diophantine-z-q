# Prescribed final prime, paired derivatives, and what extra helpers buy

This is for the same actual positive squarefree $\beta,\theta$ of one
literal Ready pole, using the selected original $E_d:y^2=x(x-d)(x+3d)$.
It preserves the original $\beta$ mark. It furnishes no new pole, actual
production rank, unconditional paired nonvanishing, or Lean build.

## 1. Exact prime progression and the missing simultaneous moment

Fix the type-one helpers $I_i$ after $\theta$ and let
$A=\beta\prod I_i$, so $A\equiv17\bmod24$, $\theta\equiv1\bmod24$,
and both are squarefree with disjoint support. The preceding common
sharp construction gives one consistent joint row for $q_0$: its
Legendre symbols at every prime dividing $A\theta$ and its type
$7\bmod12$ are fixed. One can fix a single compatible reduced
residue class $\rho\bmod M$, with $M$ divisible by
$24\prod_{r\mid A\theta}r$. Fix also any required finite exclusions and
lower bound. Every prime $q\equiv\rho\bmod M$ outside those exclusions
satisfies that same row, gives literal parameters $Aq,A\theta q$,
and preserves both actual full Sel₂ sizes and both marks. This
freedom is exact, not an independent re-selection of the companion.

Let $f_A,f_{A\theta}$ be the weight-two newforms of $E_{-A}$ and
$E_{-A\theta}$. Both are positive-discriminant twists of the
original conductor-48 form; their levels are $48A^2$ and
$48(A\theta)^2$. For $q\equiv7\bmod12$, $-q$ is fundamental and
prime to both levels. Their twists by this **same** $\chi_{-q}$
are exactly $E_{Aq}$ and $E_{A\theta q}$. Both have sign $-1$
since their actual parameters are $11\bmod12$. For $\theta>1$
the two fixed forms are distinct; if $\theta=1$ the problem
degenerates to a single derivative in the same prime progression.

A precise sufficient missing assertion is a nonzero value (beyond
any fixed exclusions) for the true mixed sum
$$
\mathcal M_{A,\theta;\rho,M}(X;W)
 =\sum_{\substack{q\ {\rm prime}\\q\equiv\rho\bmod M}}
      W(q/X)\log q\,
      L'(1,f_A\otimes\chi_{-q})\,
      L'(1,f_{A\theta}\otimes\chi_{-q}),
$$
for some fixed nonnegative smooth $W$ supported in $[1,2]$ and
sufficiently large $X$. Any asymptotic with nonzero leading main
term in this scope suffices. Nonzero sum alone suffices, regardless
of signs, because at least one product is nonzero. Separate
one-form nonvanishing results do not guarantee a common $q$.
The simultaneous product is also the second Taylor coefficient
of the *same* base-change $L$-function over $\mathbb Q(\sqrt\theta)$
for $\theta>1$, since both values themselves vanish; a first
derivative over this real quadratic field is not the target.
On the same positive $q$, classical Gross–Zagier–Kolyvagin
provides both ranks, and the established Sel₂-to-mark consumers
return both original marked points.

## 2. More helper factors: two independent fixed CRT classes really suffice algebraically

Start with any one already legal (rank-unknown) pair $n_*,n_*\theta$,
$q_0\mid n_*$, constructed on the same pole. For a fresh list
$R=\{r_1,\dots,r_k\}$ use:
- every $r_i\equiv1\bmod24$;
- every old support prime in $n_*\theta$ has both directions of square
  incidence with $r_i$, except $(q_0/r_i)=(r_i/q_0)=-1$.

These are fixed old-prime CRT conditions, feasible by Dirichlet and
reciprocity ($r_i\equiv1\bmod4$). Both deleted-$q_0$ sharp matrices
for $n=n_*\prod R$ and $n\theta$ are block diagonal: the entire
original respective sharp remains, and the common additional
block is
$$
D_R=I_k+L_R\quad\hbox{over }\mathbb F_2,
$$
where $L_R$ is the row-sum-zero internal nonsquare-symbol Laplacian of
the new list. Indeed cross-edges to old *retained* rows vanish, and
the omitted $q_0$ contributes one to each new diagonal. Every new
column has selector entry zero and its $\lambda=(3/r_i)$ bit is zero.
The old $\beta$ kernel extends by zeros: older rows see no new
marked prime, new rows see total zero against $\beta$, and even
the $q_0$ row is unchanged on the mark (its mark entry is zero).
The residue $11\bmod12$ and actual exceptional local conditions
remain unchanged.

Consequences:
1. One or **two** such extra prime factors preserve the exact card-eight
   marked Sel₂ on each twist **without any mutual prime-pair
   restriction**. For $k=2$, $D_R$ is either $I_2$ or the transposition
   matrix, according to the one internal bit.
2. Any finite number preserves it if pairwise square among the $r_i$,
   in which case $D_R=I_k$. More generally the exact test is
   $\det D_R\ne0$. For $k\ge3$ it is not automatic.
3. If accepting $q_0$ itself as the last variable instead of fixing
   it first, one can leave the internal graph arbitrary and use its
   independent bits at the new primes for graph-dependent diagonal
   completion on the **same** small/full extra block. The old edges
   at $q_0$ are kept. No harm to the marked Selmer construction,
   but the allowed $q_0$ congruence now depends on $R$; this does not
   divorce the analytic and arithmetic choices.

Thus a genuinely weaker analytic family can use the whole product
of two independent prescribed-prime classes: fix $q_0$ in a legal
row; let $r,s$ independently range in two (possibly equal) fixed
CRT classes as above, $r\ne s$; twist both fixed $E_{n_*}$ and
$E_{n_*\theta}$ by $\chi_{rs}$. The mixed sum over this biprime
family needs **no** variable Jacobi correlation weight, and
would give the desired conclusion if nonzero. This removes an
arithmetic graph obstacle for the biprime route, not the
simultaneous analytic nonvanishing obstacle.

## 3. A structural support restriction survives even unboundedly many helpers

For any literal original marked $(\beta,1)$ on $E_d$, every new odd
prime $r\ge5$ dividing the squarefree $d$ but not $\beta$ satisfies
$(\beta/r)=+1$. This is necessary independent of how Sel₂=8 was
proved. At $r\mid d$, in the $(x+3d,x-d)$ convention, the rational
2-torsion local images of $(0,0)$ and $(d,0)$ have independent
valuation pairs $(1,1)$ and $(1,0)$. Their span is the whole local
image: at odd $r$, $E_d(\mathbb Q_r)$ has an open pro-$r$ subgroup
on which multiplication by 2 is bijective, so the index of
multiplication by 2 equals the order of the local 2-torsion, four.
Thus the common zero valuation pair in this image is just the
identity. Since $(\beta,1)$ has both valuations zero, $\beta$ must
be a local square. This also applies after modifying a representative
by global torsion and returning to the exact original mark.

The actual $\beta$ includes 17, hence is nonsquare. Variable
squarefree auxiliary products are supported on splitting primes of
the fixed real quadratic field $\mathbb Q(\sqrt\beta)$, apart from
fixed finite exceptions. Even allowing arbitrarily many factors this
set has natural density zero. For any fixed finite set of inert
primes the limiting upper density is bounded by the product of
their $(1-1/r)$; since reciprocal inert primes diverge (quadratic
prime progressions), those products tend to zero. In particular,
even a density-one analytic-rank theorem over all sign-correct
squarefree twists of an arithmetic progression would not prove
nonvanishing here: every allowed marked multiplier could lie in
its exceptional set. Freezing the exact old residue of the product
also does not enforce the new internal graph beyond two factors.

## 4. Exact arithmetic control: same complete old residue, different true Sel₂

Use model packet $\beta=17,\theta=13,q_0=19$, $n_*=323$,
$n_*\theta=4199$. This is a valid all-place marked algebraic test
pair, not a production pole. Take the two triples
$$
R_{\rm neutral}=(371281,\,4200769,\,6115513),\qquad
R_{\rm path}=(371281,\,472057,\,1177489).
$$
All factors are prime and individually $68953\bmod100776$, for
$100776=24\cdot17\cdot13\cdot19$. In particular both triples
satisfy **every** fixed old-prime condition in section 2, and both
products are $79561$ modulo that same modulus. The first has
three zero internal bits, while the second gives a path with two
nonzero bits; their $D_R$ row masks are respectively $(1,2,4)$
and $(7,1,1)$.

The plain exact replay also reconstructs actual local images and
does row reduction for both enlarged curves. Result: full Sel₂
dimensions $(3,3)$ versus $(5,5)$, not merely a sharp determinant
test. The singular case retains $\beta$ but adds the independent
first-only class $472057\cdot1177489=555841924873$ on both curves.
At the odd bad support the torsion argument just given determines
the exact local image; at odd good primes all unit pairs are
unramified local Kummer classes. At infinity the allowed sign
pairs are the matching ones. At $2,3$, curves with the same positive
parameter class as 11 or 23 give exact local coordinates. The
2-adic sample $x=20$ plus torsion gives all eight pairs (each cubic
value is a nonzero local square, replay verified); at 3 the torsion
pairs already give four. This verifies mathematical full local
conditions; there is no analytic evidence for these large toy pairs.

## 5. Established analogues and why none provides the required row

- [Zhou, Theorem 1.1](https://arxiv.org/pdf/2503.14680#page=2)
  is a genuine mixed derivative moment, but assumes **odd levels**
  and varies squarefree $8d$ over a thick family, neither the
  prescribed odd prime row here nor the biprime splitting/CRT family.
  Our levels $48A^2,48(A\theta)^2$ are effectively even (in particular
  their conductors have 2-adic valuation four). The twist sign
  simplification does not remove this issue.
- [Kriz–Li, prime twists](https://www.math.columbia.edu/~chaoli/PrimeTwists.pdf)
  gives a genuine prescribed-prime approach in its isogeny scope.
  The actual isogeny class does not meet its particular one rational
  2-torsion / no rational cyclic 4 assumption (see prior exact
  restricted audit). It does not supply simultaneous nonvanishing
  for two arbitrary seed twists.
- [Thorner, Theorem 1.6](https://arxiv.org/pdf/1401.6677) provides
  nearby different primes with rank conclusions for the congruent
  number curve, not one common prime for these two non-CM forms.
- [Wong, Theorem 1](https://arxiv.org/pdf/math/0606405) gives common
  positive-rank squareclasses without the required prime factor or
  marked local support conditions.
- [Wei–Zhai, Theorem 1.1](https://doi.org/10.1093/imrn/rnag278)
  gives rank-one twists for one curve from positive definite binary
  forms under its hypotheses. It neither gives joint derivatives nor
  the real quadratic split-support and old-prime row condition.
  Representability of one multiplier by a norm form is not the dual
  factorwise/graph condition proved above.

The missing assertion is exactly a supported mixed prime-moment
nonzero value or a supported mixed **biprime** nonzero value (or
one exact qualifying numerical witness) on these literal forms.
Neither enlarging graph possibilities nor importing a thick
unconditioned averaging theorem proves that assertion.

## Replay

    python3 -B verify_joint_helper_support.py | cmp - EXACT-HELPER-BLOCK-CONTROLS.json
    sha256sum -c SHA256SUMS

No Lean build, production point, or branch write.
