# Constructing a nonzero weighted genus trace on one actual detector arm

Fix an actual original linear-\(q\) **Ready** detector \(b\), with all its
already chosen source data. Write
\(\beta=17\prod_{p\in\mathcal B}p=[17b]\) with
\(|\mathcal B|=6\), every \(p\in\mathcal B\) congruent to \(1\bmod408\),
and \(\theta=[1-b/17]\). This uses the original protected relations
\((\beta,\theta)=1\), \(\theta\equiv1\bmod24\),
\((\theta/p)=+1\) at every \(p\mid\beta\) and
\((\beta/t)=+1\) at every \(t\mid\theta\).
The auxiliary primes below are **reselected**, not modifications
of \(b\), its source index, or a previously fixed arithmetic certificate.

There are a common helper product \(I\) and a common fresh prime \(q_0\)
with
\[
 n_1=\beta I q_0,\qquad n_2=\beta I q_0\theta,\qquad
 n_i\equiv23\bmod24,
\]
such that both exact original marks and both Selmer eights hold,
and such that for \(s=n_1/17\) the analytic Sha of \(E_s\) in the
normalization of the tiling-number paper is an odd square. It follows
unconditionally that the **\(\chi_{17}\)-weighted** original level-48
Heegner trace for \(n_1\) is nontorsion, but on the **fixed curve**
\(E_{-17}\), not on the desired \(E_{n_1}\). Its precise normalizing
power of 2 relative to a fixed reference trace is derived below.

## 1. Joint finite graph, with a controlled omitted-17 minor

Use the additive Legendre matrix \(L\), row sums zero and
off-diagonal \(L_{ij}=[(p_j/p_i)=-1]\).
The selector's core is \(C=(L+\lambda a^{\mathsf T})^{q_0}\)
with the \(q_0\) row and column deleted,
\(\lambda_i=[(3/p_i)=-1]\) and \(a=e_{17}+e_{q_0}\).
The published finite theorem requires distinct primes prime to 12,
the total residue \(11\bmod12\), \(a\cdot\beta=1\),
\(\sum a_i=0\), \(L\beta=0\), and invertible \(C\).
Here a squareclass such as \(\beta\) in a matrix expression denotes its
prime indicator vector. Crucially this theorem accepts arbitrary
finite index types: no particular number of helper vertices is a
premise. See the exact file
`ActualTwoDescentFiniteConclusion318.lean`,
SHA-256 `0753c3110ab20907e1391cd8dc6682da893c39fccf749be7b8f4c2e35ae409df`,
and the all-place/cardinality receiver
`ActualTwoDescentAllPlacesExactCardinality318.lean`,
SHA-256 `d67a8a60e7e4807eca5397cb8c3236a36b2d5f7100044fed6b3031a29f85`
(the published exact receiver is also pinned by the balanced selection).

For the first arm use all helpers \(1\bmod24\), and \(q_0\equiv7\bmod24\).
All Legendre edges in the first graph are symmetric by reciprocity,
since only \(q_0\) is negative modulo 4. No fixed edge incident to
17 inside \(\mathcal B\) is nonzero, since \(\mathcal B\) consists of
primes \(1\bmod17\). Retain all fixed genuine edges inside \(\mathcal B\).
Pick one \(p_*\in\mathcal B\), and prescribe the following helper rows.

- A single \(r_0\) and \(q_0\) both have \(\beta\)-incidence
  \(e_{17}+e_{p_*}\) and have an edge to each other.
- Fix a tree on \(\mathcal B\). For every edge whose membership in the
  fixed graph differs from that in the chosen tree, add a pair of type-I
  helpers \(r_e,s_e\). Both helpers have \(\beta\)-incidence
  \(e_i+e_j\) for that edge. The two helpers are adjacent to each
  other, and only \(r_e\) is adjacent to \(q_0\).
- There are no further helper-helper edges. All new helper primes,
  including \(r_0\), have square character against every prime
  dividing \(\theta\), in both directions.

Every outside vertex has an even number of neighbors in \(\beta\),
and every \(\beta\) vertex has an even number of outside neighbors.
Thus \(L\beta=0\). In the first deleted sharp matrix the correction
is only \(e_{17}e_{17}^{\mathsf T}\): on the retained primes,
\(\lambda_{17}=1\) and the others have \(\lambda=0\).
The helper block is a direct sum of \((1)\) at \(r_0\) and
\[
 H=\begin{pmatrix}0&1\\1&1\end{pmatrix}
\]
at every pair. These diagonal entries are the true row sums including
the chosen edges to \(q_0\). The Schur correction of a pair with common
incidence \(v=e_i+e_j\) is \(v v^{\mathsf T}\), since the sum of all
entries of \(H^{-1}\) is 1. The one-vertex helper adds the analogous
rank-one matrix on \(17,p_*\). Hence the Schur complement on \(\beta\)
is the Laplacian of the chosen tree with 17 adjoined by one edge,
plus \(e_{17}e_{17}^{\mathsf T}\). This is invertible (a reduced tree
Laplacian has determinant 1). Consequently the actual first \(C\)
is invertible for **every** fixed genuine-contact graph.

Let \(B=L(s)^{q_0}\) be the *recomputed* reduced Laplacian on the
primes of \(s=n_1/17\). There are exactly two nonzero 17-edges in the
first full graph, to \(r_0,q_0\), so \(L_{17,17}=0\).
With \(e=e_{r_0}\) on the retained non-17 vertices, the actual first
deleted sharp matrix decomposes as
\[
 C=\begin{pmatrix}1&e^{\mathsf T}\\e&B+ee^{\mathsf T}\end{pmatrix}.
\]
The \(ee^{\mathsf T}\) is exactly the effect of retaining the
17-edge in the \(r_0\) diagonal. Thus eliminating the \((1,1)\)
entry shows \(\det B=\det C=1\). By
[Quadratic twists of tiling number elliptic curves, Proposition 4.2(iii)](https://arxiv.org/pdf/2405.11132)
the parity of \(g(s)=\#2\,\mathrm{Cl}(\mathbf Q(\sqrt{-s}))\)
is the bordered determinant, which here is exactly this \(q_0\)
principal minor. Equivalently the imaginary field has 4-rank zero.
One may also use the signed-prime Rédei matrix: there is only one
negative prime discriminant, \(-q_0\), and its inserted sign has
square character at all other prime factors.

For the second arm keep all these same prescribed edges and append
the distinct prime factors of \(\theta\). On every old \(\beta\) row,
the new sum of incidences is zero by \((\theta/p)=+1\); on all
helper rows it is zero by choice. Thus the original sharp block
including its diagonal is unchanged. Every new row has zero
\(\beta\)-incidence sum by \((\beta/t)=+1\), so the mark persists.
Append these new vertices one at a time. Their off-diagonal rows
and columns are fixed; each new diagonal is freely adjusted by
\((q_0/t)\) to make its Schur pivot one. The previously kept block
already includes its final diagonal throughout this process.
The distinct \(\theta\)-prime bits are compatible with the old
\(q_0\)-bits by CRT. This gives the same original two eights, with
the exact mark \((\beta,1)\) for each and *one* shared \(q_0\).
Nothing changes the fixed \(\theta\), but the split here is deliberately
\(1,\theta\), not a balanced conductor saving.

To realize the graph, choose each helper in a progression \(1\bmod24\)
with the prescribed Legendre signs against the fixed \(\beta,\theta\)
and earlier helpers. Reciprocity gives the reverse signs against
old \(1\bmod4\) primes. After they are chosen, choose \(q_0\equiv7\bmod24\)
with the specified signs at all old and new vertices. Dirichlet
gives these choices, with any finite avoidance and lower bound.
The complete finite check therefore needs no distribution assertion
about the fixed genuine-contact Legendre graph or its factor order.

## 2. The actual weighted genus trace and its exact relative index

Write \(E_n:y^2=x(x-n)(x+3n)\) and \(E_0=E_{-1}\) for the fixed
modular quotient, so \(E_0^d=E_{-d}\).
For an odd squarefree \(n=17s\equiv23\bmod24\), set \(D=-n\),
\(K=\mathbf Q(\sqrt D)\), \(H/K\) its Hilbert class field, and choose
the original 48-ideal \(\mathfrak n=\mathfrak p_2^4\mathfrak p_3\).
Both 2 and 3 are split in \(K\). The coprime fundamental
discriminants \(17,D/17\) give the genus field \(K(\sqrt{17})\subset H\).
Let \(\chi_{17}\) be its order-two class character and define
\[
 R_{17}(n)=\sum_{a\in\operatorname{Pic}(\mathcal O_K)}
                   \chi_{17}(a)\phi(x_a).
\]
The nontrivial weights sum to zero, so centering the modular map
by a rational cusp does not change this point. It transforms via
\(\chi_{17}\) under \(\operatorname{Gal}(H/K)\).
By the actual Fricke identity
\(\phi w_{48}=T_3-\phi\) and reversal of the original orientation,
complex conjugation acts on this weighted trace by
\(-\chi_{17}(\mathfrak n)=+1\), since
\(\chi_{17}(\mathfrak p_2)^4\chi_{17}(\mathfrak p_3)
=(17/2)^4(17/3)=-1\). Thus \(R_{17}(n)\) belongs to the
\(\sqrt{17}\)-anti-invariant part of \(E_0(\mathbf Q(\sqrt{17}))\),
and descends to a rational point \(Q_{17}(s)\) on the fixed \(E_{-17}\).

The exact complete oriented CM orbit at \(D=-119\) has classes
\(\mathfrak p_2^k\mathfrak p_3^j\) with \(k=0,\ldots,4\), \(j=0,1\).
The normalized \(\chi_{17}\) is \((-1)^j\) up to a common sign,
harmless for height. The pinned exact mod-29 values, reaggregated
by the separate replay here, give
\(R_{17}(119)=(7,24\sqrt2)\) and
\([4]R_{17}(119)=(18,19\sqrt2)\ne O\) in that calibration.
Reduction at 29 is good and the torsion of \(E_{-17}(\mathbf Q)\)
is just \(E_{-17}[2]\) by the tiling paper's Lemma A.3.
Thus \(Q_{17}(7)\) is nontorsion.
This is a fixed reference for the weighted trace, not a selected
original detector point.

[Cai–Shu–Tian, Theorem 1.1](https://arxiv.org/pdf/1408.1733)
applies to both \(D\) and \(-119\):
\(N=48\) is prime to \(D\), both bad-level primes split,
the character has ring-class conductor 1 and both quadratic
orders have only the units \(\{\pm1\}\).
In the formula the \(D\)-dependent scalar for our fixed parametrization
is \(1/\sqrt{|D|}\); the degree, Petersson norm and equal-degree
height normalization cancel in the comparison. Artin formalism gives
\[
 L(E_0/K,\chi_{17},z)=L(E_{-17},z)L(E_s,z).
\]
Since \(E_{-17}\) has sign \(-1\) (Lemma A.4), the positive
height at \(s=7\) implies \(L'(E_{-17},1)\ne0\).
Gross–Zagier–Kolyvagin then gives rank one for the fixed \(E_{-17}\).
Quadratic twist descent preserves the normalized canonical height.
Cancelling the fixed derivative therefore gives
\[
 \frac{\hat h(Q_{17}(s))}{\hat h(Q_{17}(7))}
       =\sqrt{\frac{s}{7}}\frac{L(E_s,1)}{L(E_7,1)} .
\]
Here the meaning is valid also if the numerator is zero.

For \(s\equiv7\bmod24\), use the tiling paper's Eq. (1.1),
Lemmas A.3, A.5, A.6: the period is \(\Omega_E/\sqrt{s}\),
the two fixed Tamagawa numbers are both 2, every prime dividing
\(s\) gives Tamagawa number 4, and rational torsion has order 4.
Hence
\[
 L(E_s,1)\sqrt{s}=
   \Omega_E\,4^{\omega(s)-1}\mathcal L(s),
\]
where \(\mathcal L(s)\) is its analytic Sha number.
At \(s=7\), Theorem 2.8 gives \(\mathcal L(7)=1\)
(the only solutions of \(x^2+3y^2+12z^2=7\)
are \(x=\pm2,y=\pm1,z=0\)).
By Proposition 2.6(ii) and Theorem 2.7 the number
\(\mathcal L(s)\) is a square of an integer, odd for our chosen
determinant \(g(s)\). Thus if \(m_s,m_7\) are the respective
coefficients of \(Q_{17}(s),Q_{17}(7)\) in a fixed primitive
generator of the rank-one group modulo torsion, then
\[
 |m_s|=2^{\omega(s)-1}\sqrt{\mathcal L(s)}\,|m_7|,
 \qquad v_2(m_s)=\omega(s)-1+v_2(m_7).
\]
In particular an exact normalized odd multiplier has been
obtained **for this weighted component** without computing
the enormous actual \(s\) or its CM class orbit.

The unweighted trace on \(E_{n_1}\) and both original marked
rational points are still unknown. The weighted point just proved is
on a different curve; its large forced factor of 2 also shows why
a single rational halving cannot transfer its nonzero free part.
A genus induction or a deeper exact comparison of the two different
components would require a separate argument. No rank, mark or
nonzero primitive coefficient is claimed for \(E_{n_1}\) or \(E_{n_2}\).

## Replay

With the pinned `D=-119` donor JSON as the single argument:
```sh
python3 -B replay_weighted_genus.py EXACT-INERT-CM-PILOT.json | cmp - EXACT-WEIGHTED-GENUS-CONTROLS.json
sha256sum -c SHA256SUMS
```
The graph replay tests every six-vertex fixed contact graph.
The pinned donor SHA-256 is
`8cfca028b915bd6c059853447faeb5c50bbee67f58ac4816e4b25f336bfcc85d`.
