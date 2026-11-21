# One common prime gives two nonzero weighted genus traces

Fix one actual original linear-\(q\) Ready detector \(b\).
Retain its exact source data and \(\beta=[17b]\),
\(\theta=[1-b/17]\). The first-arm construction and the normalized
height comparison are inputs from the exact
`original-detectors-chi17-weighted-construction-r1` proof,
checksum-list digest
`7af62937f312eeaac3014ab0583efb7e81acb7fa4e02414bc569427a8597e835`.
Here a new shared helper per prime of \(\theta\) controls **both**
even companions; it does not preserve a previously selected helper
roster or final prime.

Let \(I\) be the first proof's helper product for the fixed genuine
contact graph, but not yet set \(q_0\). Write \(S=\operatorname{supp}\theta\).
Choose distinct additional shared type-I primes \(r_t\equiv1\bmod24\)
for \(t\in S\). None is in the old support or \(S\). Put
\(I'=I\prod_{t\in S}r_t\). The pair will be
\[
 n_1=\beta I' q_0,\qquad n_2=\beta I' q_0\theta,\qquad
 s_i=n_i/17,\qquad q_0\equiv7\bmod24.
\]
No bound on the size of the selected primes is asserted.

## A reserve incidence block preserves both exact gates

Use additive Legendre edges, so an edge means nonsquare. Every reserve
\(r_t\) has:
- no edge against any old \(\beta\) prime, old helper, or other reserve;
- an edge against its own \(t\), and no edge against any other prime
  of \(\theta\);
- an edge against the chosen common \(q_0\).

These signs hold in both directions by reciprocity, because all the
reserves are \(1\bmod4\). They can be imposed by successive CRT and
Dirichlet choices; the last condition is imposed on \(q_0\) together
with the first-proof \(q_0\)-edges. The \(q_0\) signs at the
\(\theta\)-vertices may now be chosen arbitrarily, since they affect
only diagonal entries which are immaterial below. All original
finite avoidance requirements can be retained.

The first arm does not contain the \(\theta\)-vertices. There each
reserve is detached after deleting \(q_0\), with diagonal one from
the \(q_0\)-edge. It also has no 17-edge. Thus both the first sharp
matrix and the first reduced Laplacian on \(s_1\) are the matrices
of the first proof augmented by an identity reserve block.

On the second arm each reserve diagonal is zero, because it now
has its one corresponding \(\theta\)-edge as well as its
\(q_0\)-edge. After deleting \(q_0\), the couplings from \(\theta\)
to reserves and from reserves to \(\theta\) are exactly identity
matrices. Every old \(\beta\)-row gains zero total \(\theta\)-incidence,
since \((\theta/p)=+1\) at every \(p\mid\beta\); the old helpers
were chosen square against all of \(\theta\). Thus the old sharp
block, before reserves or \(\theta\), is precisely the old
invertible first sharp block \(C\). On the omitted-17 side the old
recomputed Laplacian block is precisely the old invertible
first reduced Laplacian \(B\): 17's new edges can alter only
\(\theta\)-diagonals on removal. No reserve has a 17-edge.
The same two matrices in the second arm have the forms
\[
 \begin{pmatrix}C&J_C&0\\ K_C&T_C&I\\0&I&0\end{pmatrix},\qquad
 \begin{pmatrix}B&J_B&0\\ K_B&T_B&I\\0&I&0\end{pmatrix}
\]
in the order old, \(\theta\), reserves. No transpose relation or
invertibility is required of \(J_*,K_*,T_*\). Indeed a kernel
vector has zero \(\theta\) part by the reserve equations, zero
old part by \(C\) or \(B\), then zero reserve part by the
\(\theta\)-equations. In particular \(\lambda_t\)'s sharp
correction at column 17 is allowed, since it belongs only to
\(K_C\). The case \(S=\varnothing\) is the first proof.

The exact \(\beta\) indicator persists: the old rows are unchanged
on its evaluation, each new \(\theta\)-row has \((\beta/t)=+1\),
and every reserve row has no \(\beta\)-edge. The original
\(a=e_{17}+e_{q_0}\) still has sum zero and \(a\cdot\beta=1\).
The native finite theorem and its all-place receiver thus give both
exact original Selmer eights, with their literal marks on the same
\(b\). This verification uses the actual directed Legendre rows
at the \(\theta\)-primes, not an artificial symmetric approximation.

## What the two gates give, and what they do not

Both \(s_i\equiv7\bmod24\). By Proposition 4.2(iii) and
Theorem 2.7 of the [tiling-number paper](https://arxiv.org/pdf/2405.11132)
the actual reduced unsigned Laplacian minor on each \(s_i\)
gives \(g(s_i)\) odd and \(\mathcal L(s_i)\) an odd square.
This formula applies also when several primes of \(s_2\)
are negative modulo 4: it is the bordered determinant of their
actual row-sum-zero additive Legendre matrix, and expansion of the
border with \(e_{q_0}\) gives our principal minor.

Apply the first proof's exact genus-character and
[Cai–Shu–Tian height comparison](https://arxiv.org/pdf/1408.1733)
to each \(n_i=17s_i\), with the same fixed reference \(D=-119\).
Both weighted traces descend to **the fixed curve \(E_{-17}\)**.
If \(m_i\) and \(m_7\) denote their free coordinates in its rank-one
Mordell–Weil group, then
\[
 |m_i|=2^{\omega(s_i)-1}\sqrt{\mathcal L(s_i)}\,|m_7|\ne0,
 \qquad v_2(m_i)=\omega(s_i)-1+v_2(m_7).
\]
These are genuinely two weighted comparisons from a single selected
pair, not two separately chosen \(q_0\)'s. They still supply **no**
unweighted nonzero trace, rank, or marked rational point on either
moving curve \(E_{n_i}\). Nor do they assert a source anchor or
complete the shared-index PointPair construction.

The finite replay tests explicit directed Legendre graph completions,
including negative reciprocity, physical 17-\(\theta\) edges and
nonzero 3-symbols at \(\theta\).
