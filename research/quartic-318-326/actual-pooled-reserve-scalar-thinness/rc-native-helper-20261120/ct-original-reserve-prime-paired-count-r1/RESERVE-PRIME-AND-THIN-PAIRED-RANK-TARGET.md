# One reserve prime thickens the exact marked simultaneous twist family

Fix **one literal Ready pole**, its positive squarefree \(\beta=[17b]\)
and \(\theta=[1-b/17]\), and one pair selected by the original simultaneous
matrix construction:
\[
 n_*=\beta q_0\prod I_i,\qquad n_*\theta .
\]
The original construction gives squarefree positive twists \(11\bmod12\),
two actual full Selmer groups of size eight and the same marked class
\((\beta,1)\). We use its actual invertible deleted sharp matrices, its
seed selector with zero entries on any further vertices, and the mark
kernel. For the optimized detector seed matrices these are in
[the same-pole companion construction](../ct-linear-q-companion-paired-r1/COMPANION-THETA-PAIRED-SELECTION.md);
for any of the four Ready poles use the original arbitrary-support
simultaneous matrix theorem described in the
[original source assembly](../../joined-work-20261120/linear-q-original-forward-one-rank-input-r1/SAME-INDEX-ORIGINAL-318-AND-326-FORWARD-WITH-ONE-RANK-INPUT.md),
with its sharp witness *before* applying the native cardinality consumer.
No numerical pole or numerical rank is asserted.

## 1. Unboundedly many auxiliaries, without designing their internal graph

Let \(P\) be the distinct prime support of \(n_*\theta\), so \(2,3\notin P\).
The only fixed excluded primes required here are \(\{2,3\}\cup P\);
any additional fixed finite exclusions can simply be discarded. Put
\(M=12\prod_{p\in P}p\). Let \(\mathcal C\subseteq(\mathbb Z/M)^\times\)
consist of all residues \(c\) with \(c=1\bmod12\) and
\[
 (c/p)=+1\quad(p\in P\setminus\{q_0\}),\qquad (c/q_0)=-1.
\]
It is a nonempty **union** of reduced classes. Its exact relative prime
density is \(\delta=|\mathcal C|/\varphi(M)=2^{-|P|-2}\) by CRT. One may
instead fix any nonempty subunion, or impose more compatible old-place
conditions, with its own positive density. Additional finite prime exclusions
do not change the density. Reciprocity gives the same incidence in both
directions since every new prime is \(1\bmod4\).

Take **any** squarefree product \(R\) of primes in those classes, including
\(R=1\); nothing is imposed between its own factors. Adjoin a new reserve
prime \(s\) in the same classes. The old retained blocks on both twists
are untouched: each old retained row sees zero incidence from every
new prime. Each newly retained row sees exactly one nonsquare old
incidence, to the omitted vertex \(q_0\). The new \((3/r)\) entries and
the new selector coordinates are zero, so the one common new block is
\(I+L\), with \(L\) the internal graph Laplacian over \(\mathbb F_2\).
The old marked vector extends by zero; neither a retained row nor
the already fixed deleted row \(q_0\) gains a contribution from a
nonzero marked coordinate. All new factors are \(1\bmod12\) and disjoint
from the whole old support. This is exactly the preserved-block argument
of the [previous two-helper theorem](../ct-joint-q0-derivative-and-helper-support-r1/JOINT-PRIME-ROW-DERIVATIVES-AND-HELPER-SUPPORT.md),
but here the number and internal graph need not be designed in advance.

**Reserve lemma.** Write \(m=\omega(R)\), and \(b_i=[(s/r_i)=-1]\).
At least one of the \(2^m\) rows \(b\) makes the common new block
invertible. If \(m\) is odd, at least two rows work, one for each prescribed
value of the last bit. In particular at least a \(2^{-m}\) fraction
of the permitted reduced \(s\)-residues modulo \(MR\) work.

Indeed, let \(D_R=I_m+L_R\) (not assumed invertible) and
\(A=D_R+\operatorname{diag}(b)\). The enlarged matrix has blocks
\(A,b,b^{\mathsf T},1+\sum b_i\). Replace the last basis vector by the
all-ones vector, simultaneously in rows and columns. The enlarged matrix
has row sum one, so this yields
\[
                  \begin{pmatrix}A&\mathbf 1\\ \mathbf 1^{\mathsf T}&m+1\bmod2\end{pmatrix}.
\]
If \(m\) is even, the determinant is that of \(A+\mathbf1\mathbf1^{\mathsf
T}\) by the Schur complement of the final 1. It is multiaffine in the
\(b_i\), with coefficient 1 on the product of all \(m\) variables. Its
sum over binary inputs is 1 in \(\mathbb F_2\); hence it is not
identically zero, including the case \(m=0\).
If \(m\) is odd, replace the first \(m-1\) old basis vectors by
\(e_i+e_m\), retaining \(e_m\) and the final all-ones vector.
Expansion at the final row and column gives the determinant of the
restriction of \(A\) to the first \(m-1\) difference vectors.
For either fixed \(b_m\) that is a fixed matrix plus the free
diagonal \(\operatorname{diag}(b_1,\dots,b_{m-1})\), so the same
multiaffine argument applies. Each bit row is realized by exactly
\(\varphi(R)/2^m\) reduced residue classes modulo \(R\), independently of
the \(s\bmod M\) choice. This proves the stated fraction, without any
statistical assumption on the internal Legendre symbols.

Thus for every such \(R\), appending a prime \(s\) in one of these
residue classes retains both exact Selmer eights and the original mark
on
\[
                       E_{n_*Rs},\quad E_{n_*\theta Rs}.
\]
This does **not** replace or reselect \(q_0\), nor vary \(\beta,\theta,b\),
the original source index or any of its detector and scalar rows. No
cross-pole prime equality is required by the source consumer.

## 2. Unconditional lower bound for distinct actual paired parameters

For sufficiently large \(X\), count the preceding pairs with
\[
                 R\le X^{1/4},\qquad X/R<s\le 2X/R.
\]
Then \(s>X^{3/4}\) while every prime in \(R\) is at most \(X^{1/4}\);
the reserve prime is therefore uniquely recovered from \(m_*=Rs\).
The products \(m_*\in(X,2X]\) counted are genuinely distinct, not
multiple representations. There is no \(s\mid MR\). Let \(G_R\) be the
reduced classes modulo \(MR\) specified by the reserve lemma and the
old row. Then \(|G_R|/\varphi(MR)\ge\delta\,2^{-\omega(R)}\).

Use [Bombieri–Vinogradov](https://doi.org/10.1112/S0025579300005313)
in its maximal-argument and maximal-class version, with the prime-only
Chebyshev function \(\vartheta(y;q,a)\). The prime-only version follows
also from the version for \(\psi\): the omitted prime powers contribute
\(O(\sqrt T\log^2T)\) per modulus, absorbed by increasing the log cutoff
in the maximal theorem. Write \(E(T,q)=\max_{y\le T,(a,q)=1}
|\vartheta(y;q,a)-y/\varphi(q)|\). For \(R\in[Z,2Z)\) and \(R\le X^{1/4}\)
take \(T=2X/Z\). Both reserve interval endpoints are at most \(T\), and
\(MR\le2M Z\) is below \(T^{1/2}/(\log T)^B\) for each fixed \(B\)
and large \(X\), uniformly in these \(Z\). Every term with modulus
\(MR\) is used only once. Summing the errors over all allowed classes
and all such \(R\) costs at most
\[
 \sum_{Z\le R<2Z}2|G_R|E(T,MR)
 \ll_M Z\sum_{q\le2MZ}E(T,q)\ll_{M,A}X(\log X)^{-A}
\]
for any fixed \(A\). In particular the factor for the number of accepted
classes is included, rather than treating a union as one class.
Summing the dyadic blocks and using \(\log s\le\log(2X)\), the count is
bounded below by
\[
 \frac{\delta X}{\log(2X)}
 \sum_{\substack{R\le X^{1/4}\\R\text{ squarefree}\\p\mid R\implies p\in\mathcal C}}
            \frac{2^{-\omega(R)}}R
       -O_{M,A}(X(\log X)^{-A}).
\]
Fixed excluded primes are omitted in both sums throughout.

The sum is \(\gg_M(\log X)^{\delta/2}\). To see this without a uniform
smooth-number asymptotic, use the finite Euler product over eligible
primes \(p\le Y=X^\epsilon\), with \(\epsilon>0\) small and fixed:
\[
                         \prod_{p\le Y}(1+1/(2p))
                              \asymp_M(\log Y)^{\delta/2}.
\]
This is the fixed-modulus prime number theorem and partial summation
applied to the logarithm of the product. Normalize its terms to a
probability law on squarefree \(R\): inclusion of \(p\) has probability
\(1/(2p+1)\). The expected \(\log R\) is then
\(\sum_{p\le Y}\log p/(2p+1)\ll\log Y\) by the ordinary prime number
theorem. Choose \(\epsilon\) small enough that this is at most
\((\log X)/8\). Markov's inequality keeps at least half the product mass
with \(R\le X^{1/4}\). This proves the unconditional bound
\[
 \boxed{\#\{m_*\in(X,2X]\text{ in the same actual paired two-Selmer family}\}
          \gg_M X/(\log X)^{1-\delta/2}.}
\]
For every fixed \(k\ge1\) one may instead keep exactly \(k-1\) primes in
\(R\), each at most \(X^{1/(4(k-1))}\) when \(k>1\). Summing their
distinct products in the displayed reciprocal sum gives
\(\gg_{M,k} X(\log\log X)^{k-1}/\log X\) with exactly \(k\) new primes
(the \(k=1\) case has \(R=1\)). The reciprocal sum here is the
\((k-1)\)-th elementary symmetric polynomial of prime reciprocals;
repeated indices contribute lower order because \(\sum_p p^{-2}<\infty\).
The variable-\(k\) bound above is a single disjoint-product count, not
an interchange of nonuniform fixed-\(k\) asymptotics.

## 3. Exact target still missing on these twists

Let the two fixed base curves be the literal \(E_{n_*}\) and
\(E_{n_*\theta}\), with squarefree \(m_*\) as above, prime to their
conductors. Their *same* positive quadratic twist by \(m_*\) gives
the two selected curves. Since each fresh prime is \(1\bmod12\), both
twists still have the original root number \(-1\).
The standard Gross–Zagier–Kolyvagin implication for analytic rank one
then gives algebraic rank one, and the two actual Selmer eights
identify the same original mark as rational. This is a sufficient
route, not a conclusion of the count.

In particular, an ordinary *unrestricted* exceptional-set estimate
\(O_{E_{n_*}}(X/\log X)\) and \(O_{E_{n_*\theta}}(X/\log X)\) for
analytic rank at least two would suffice together, since their union
is \(o(X/(\log X)^{1-\delta/2})\). More generally any such estimates
little-o of the proved lower bound suffice. An \(o(X)\) density theorem
alone does not suffice, even if independently proved: the fixed mark
forces every fresh odd prime to split in \(\mathbb Q(\sqrt\beta)\)
and the resulting semigroup has density zero. The October 6
[mean-rank preprint](https://github.com/openai/math/tree/main/preprints/The-mean-analytic-rank-of-quadratic-twists-of-elliptic-curves-October-6-2026)
uses its companion density theorem for the actual mean, and its
independent high-rank tail controls ranks above a sufficiently large
threshold, not rank \(3\) on these twists.

Nor can one repair the odd-level hypotheses of
[Zhou, Theorem 1.1](https://arxiv.org/html/2503.14680v1#S1.T1) or
[Hamdar–Sabuncu, Theorem 1](https://arxiv.org/html/2607.13000v1#S3.T1)
by first changing the quadratic character or passing to an isogenous
model. On the literal equation \(E_d:y^2=x(x-d)(x+3d)\) the
discriminant is \(2^8 3^2 d^6\). The valuation at 2 for every rational
quadratic-twist squareclass is 8 or 2 modulo 12, never zero. All
Weierstrass discriminants in that rational-2-adic isomorphism class
have the same value modulo 12. Thus no quadratic twist has good
reduction at 2, also after any isogeny by the Néron–Ogg–Shafarevich
criterion. In particular there is no odd conductor model. Separately,
Hamdar–Sabuncu gives a single derivative average over an imaginary
norm family, not two derivatives on this marked split-support
family. The current [Wei–Zhai quadratic-form theorem](https://doi.org/10.1093/imrn/rnag278)
is likewise one positive-definite binary-form family with the requisite
coprimality, not a two-form simultaneous rank theorem or a verification
of either selected Selmer condition. These scope comparisons do not
assert that the corresponding methods could not be extended.

### Replay and scope

    python3 -B replay_reserve_graph.py | cmp - EXACT-RESERVE-GRAPH-CONTROLS.json
    sha256sum -c SHA256SUMS

The replay exhausts the finite graph/bit systems through five old
neutral vertices, including genuinely singular old graphs and sharp
one-row cases. The quantitative prime count is a mathematical
application of the published Bombieri–Vinogradov theorem, not a
numeric prime scan or an analytic rank computation. Neither the October
pointwise converse, a rank result, four simultaneous actual PointPairs,
nor a Lean build is claimed.
