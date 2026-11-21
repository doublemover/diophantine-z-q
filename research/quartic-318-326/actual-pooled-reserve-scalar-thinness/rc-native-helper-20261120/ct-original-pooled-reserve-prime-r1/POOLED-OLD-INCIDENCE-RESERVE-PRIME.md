# A denser actual paired family by pooling old symbols

Keep one literal Ready mark \(\beta\), its same companion \(\theta\), and its
same original selected seed and omitted prime \(q_0\), as in the
[reserve lower bound](../ct-original-reserve-prime-paired-count-r1/RESERVE-PRIME-AND-THIN-PAIRED-RANK-TARGET.md).
Use actual selected deleted sharp matrices before taking the finite
cardinality consequence. The base and companion deleted matrices have the
block form
\[
                    C,\qquad F=\begin{pmatrix}C&X\\Y&Z\end{pmatrix},
\]
respectively, both invertible, with the **same** retained base block.
Here \(d\) is the number of base retained vertices (old \(\beta\) and
old helpers, not \(q_0\)) and \(j=\omega(\theta)\).
This form is guaranteed by the original mutual-symbol/old-core
retention construction and its diagonal step, and by the optimized
construction when used. The selector is extended by zero on the
\(\theta\) part and on all new primes. These are fixed after the
original choice; no source or companion parameter is retuned.

This refinement proves at least
\[
              \gg_{C,F,q_0,\beta,\theta}
              X/(\log X)^{1-2^{-j-5}}
\]
distinct common new multipliers in \((X,2X]\) preserving the two
exact Selmer sizes eight and the same mark. The improvement over
the completely neutral pool is that the log exponent depends
on the number of \(\theta\) primes, **not** on the number of
already fixed base \(\beta\) or helper primes. No rank result follows
without the separate analytic input.

## 1. Transfer an entire old-incidence column through the old core

Write the two directed Legendre edges with the usual numerator
column, denominator row convention. For an old retained base prime
\(p\), equality of the two old sharp diagonals implies
\(\sum_{r\mid\theta}[(r/p)=-1]=0\): the old selector correction is
identical. Reciprocity and \(\theta\equiv1\bmod4\) give also
\(\sum_{r\mid\theta}[(p/r)=-1]=0\). Furthermore the sum of the
\(\theta\) coordinates of the sharp correction vector \(\lambda\)
is zero because \((3/\theta)=+1\) for \(\theta\equiv1\bmod12\).
Therefore the actual lower-left sharp block has
\[
                              \mathbf1_J^{\mathsf T}Y=0.
\]
Nothing says \(Y\) is the transpose of \(X\).

Let \(U=\{v\in\mathbb F_2^d:\beta^{\mathsf T}v=0\}\),
where \(\beta\) in this line is the original nonzero zero-one mark
restricted to the retained base indices. Let a fresh \(r\equiv1\bmod12\)
have any allowed old-base bit column \(v=v(r)\in U\). Require its
\(\theta\)-incidence column and \(q_0\)-bit to equal
\[
                 w=YC^{-1}v,\qquad
                 [(r/q_0)=-1]=1+\mathbf1_d^{\mathsf T}v.
\]
These are exact CRT conditions on the signs of \(r\) at all old primes;
reciprocity gives the displayed bit columns in both directions because
\(r\equiv1\bmod4\). They do not change the already selected \(q_0\).
There are no conditions yet between any new primes.
The \(w\)-entries sum to zero, and
\[
                        F^{-1}\binom vw=\binom{C^{-1}v}{0}.
\]
Over \(M=12\prod_{p\mid n_*\theta}p\) this small-prime pool is a union of
reduced residue classes of exact relative density
\(\delta'=2^{-2}2^{-(d+j+1)}|U|=2^{-j-4}\).
Indeed \(\dim U=d-1\); each \(v\in U\) gives one different complete old
sign vector; each vector has the same number of residue classes.

## 2. The pooled parity and one neutral reserve preserve both old problems

Take a squarefree product \(R\) of such primes with pooled
\(\sum_{r\mid R}v(r)=0\) in \(U\). Then \(\sum w(r)=0\) as well.
Adjoin a single reserve \(s\) **neutral on the old retained primes**
and nonsquare at \(q_0\), in the nonempty old neutral union of the
previous packet; this makes its \(v_s\) and \(w_s\) zero.
Both old retained blocks \(C,F\) remain literally unchanged:
their off-diagonal entries are untouched, and the old diagonal
changes are exactly the pooled incidence sums. All new type-one
vertices have \(\lambda=0\) and selector entry zero.
The original mark persists because the new rows have \(\beta\)-sum
zero, and the old diagonals on the retained mark have not changed.
The omitted \(q_0\) mark coordinate is zero, so its diagonal does
not affect this check. The original residues \(11\bmod12\) and
\(\beta\bmod24\) still hold.

Let \(V\) be the matrix of old-base columns on all new primes,
with its last column \(v_s=0\), and \(W=YC^{-1}V\).
By the \(q_0\)-bit choice and \(\mathbf1_J^{\mathsf T}w=0\), the
common new sharp block before elimination is \(I+L\), using its
arbitrary internal Legendre Laplacian \(L\). The cross blocks are
the indicated incidence matrices and their transposes, since both
sharp correction entries vanish whenever either index is a new
vertex (one of selector or \(\lambda\) vanishes). The two Schur
complements are **equal**, namely
\[
                           D=I+L+V^{\mathsf T}C^{-1}V,
\]
because the correction in the bigger one is
\([V^{\mathsf T}\ W^{\mathsf T}]F^{-1}[V^{\mathsf T}\ W^{\mathsf T}]^{\mathsf T}\).
Even if \(C^{-1}\) is nonsymmetric, the extra term has zero
row and column sums: \(V\mathbf1=0\). Its last row and column
are zero. Thus before adding the reserve, the common core for
the new primes has row sums and column sums one, and adding
the reserve at any bit row acts exactly as in the previous
reserve lemma. That lemma uses those two sum identities, not
symmetry of the old core. There are again at least a \(2^{-\omega(R)}\)
fraction of working reserve bit rows. Both actual deleted sharp
matrices are invertible for any working row, with no rank
assumption. Use the original arbitrary-index all-place cardinality
and actual Kummer identification on both.

## 3. Count while imposing the pooled parity on an unbounded pool

Choose \(R\le X^{1/4}\) and \(X/R<s\le2X/R\); the uniquely large
prime \(s>X^{3/4}\) still witnesses distinct products. The very same
maximal Bombieri–Vinogradov estimate applies to the reserve moduli
\(MR\). One charges every acceptable reduced class to its modulus
exactly as in the earlier lower bound, now with the positive
**neutral reserve density** (fixed) in the main term. The small
prime density \(\delta'\) occurs in the reciprocal sum
\[
                   \sum_{R\le X^{1/4},\ \sum v(r)=0}
                         \frac{2^{-\omega(R)}}R.
\]
To bound this from below, choose all eligible small primes \(r\le
Y=X^\epsilon\). Under normalized Euler product weights, include
\(r\) independently with probability \(u_r=1/(2r+1)\).
For every additive character \(\psi:U\to\{\pm1\}\), the factor
\(1-u_r+u_r\psi(v(r))\) is positive, because \(u_r<1/2\).
Consequently character averaging at the identity gives
\[
                  \Pr\left(\sum v(r)=0\right)\ \ge 1/|U|.
\]
This is unconditional for these exact columns; no distribution
of internal Legendre symbols or of the small primes' profiles is
assumed beyond the fixed-class prime number theorem for their union.
The expectation of \(\log R\) is \(O(\epsilon\log X)\).
Choose \(\epsilon>0\) small enough, with dependence on the fixed
\(U\), that Markov gives
\(\Pr(R>X^{1/4})\le1/(2|U|)\).
The admissible events together retain at least \(1/(2|U|)\) of the
finite Euler product \(\prod(1+1/2r)\asymp(\log X)^{\delta'/2}\).
This yields the stated bound including the exponent
\(1-\delta'/2=1-2^{-j-5}\).
The implicit constant and threshold are allowed to depend on
the particular fixed \(\theta\) and seed. There is no assertion
uniform in changing supports.

### Exact nonneutral, nonsymmetric control

The executable control uses actual primes
\(\beta=(17,73),\,\theta=(139,163),\,q_0=67\).
The two old matrices are literally evaluated from their Legendre symbols;
the companion is genuinely nonsymmetric. The two small new primes
337 and 1213 have \(v=(1,1),\,w=(1,1)\), so neither is a neutral
old-row prime. The common correction is the all-ones matrix on their
two coordinates. Exact reserve primes for all four bit rows are
included; three work, and the one failing row decreases each rank
by one. This validates the signed dependency and the common Schur
complement on numerical prime data, not that these parameters came
from a literal pole, nor any Mordell–Weil rank.

    python3 -B replay_pooled_reserve.py | cmp - EXACT-POOLED-RESERVE-CONTROL.json
    sha256sum -c SHA256SUMS
