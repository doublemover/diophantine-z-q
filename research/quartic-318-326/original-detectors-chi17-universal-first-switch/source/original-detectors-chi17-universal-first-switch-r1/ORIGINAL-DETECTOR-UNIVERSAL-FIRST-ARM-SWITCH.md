# A universal selector-preserving switch for one fixed reference bit

Fix **one actual original linear-\(q\) Ready detector**, after the four-pole source choice, and its literal squareclasses \(\beta=[17b]=17d\) and \(\theta=[1-b/17]\). The six genuine primes of \(d\) are the five contact numerators and the common denominator prime \(q\) of the published source construction. They are all \(1\bmod408\). Here \(q_0\) is the subsequent Selmer-selection prime, not the source prime \(q\). The native protected relations are \(\theta>0,\ \theta\equiv1\bmod24,\ (\beta,\theta)=1,\ (\theta/p)=1\) for \(p\mid\beta\), and \((\beta/t)=1\) for \(t\mid\theta\).

We prove that **one fixed bit**
\[
 u(d)=2^{-9}\log_2 R_{17d}(119d)\pmod2
\]
is sufficient for a whole admissible first-arm prime progression if it is \(1\). In particular, there is no odd-tree-cofactor hypothesis on the genuine graph. We retain both exact native Selmer eights for the same \(q_0\) and the same literal mark \((\beta,1)\), but prove nontorsion only on the first arm and only conditional on the bit. We do not evaluate the bit, assert that it is nonzero, or claim a companion rank.

## 1. The genuine graph in the exact source ray

Use vertices \(0,\ldots,4,5\) for contact primes \(p_i=u+k_iQ^2q\) and the prime \(q\). The contact offsets are the negatives of the five fixed rational roots
\[
  h_i=0,\ -1/2,\ -1,\ 1/2399,\ -32/407
\]
times a common nonzero rational square (the cleared \(D^2/c_j^2\) in the source theorem, with the scale of this slot). The only possible odd part of the quadratic character of the nonzero difference \(k_i-k_j\) on this source ray is its \(7\)-part. Indeed the source wheel contains the denominator and translated-norm exceptions, as well as the fixed root-difference odd divisors: outside \(7\) the selected Gaussian representative is \((0,1)\) at these fixed odd primes unless already controlled by the \(1\bmod408\) condition. Its rational norm is \(1\) at them. The latter condition also gives \((2/p_i)=(-1/p_i)=1\). At \(7\), the mandated Gaussian representative is \((1,3)\), hence the rational primes are \(3\bmod7\) and \((7/p_i)=-1\).

In binary notation put \(\mu=[(u/q)=-1]\). Since \(p_i\equiv u\pmod q\), all edges at \(q\) are \(\mu\). For distinct contact vertices, reduce
\(p_i-p_j=(k_i-k_j)Q^2q\bmod p_j\) and use reciprocity for \(q,p_j\), both \(1\bmod4\), to obtain
\[
  [(p_i/p_j)=-1]=\mu+v_7(h_i-h_j)\pmod2 .
\]
The only odd \(7\)-depths are \(v_7(h_1-h_4)=v_7(h_3-h_4)=3\). The resulting graph for \(\mu=0\) is the path \(1-4-3\) plus three isolated vertices; for \(\mu=1\) it is its complement in the complete graph on six vertices. In the fixed order \(0,1,2,3,4,5\), the row masks of the binary Laplacian \(L_d\), its nullity \(m\), and suitable coordinate indices are
\[
\begin{array}{c|c|c|c}
\mu&\text{row masks}&m&\text{indices}\\
0&(0,18,0,24,10,0)&4&(0,1,2,5)\\
1&(63,45,63,39,53,63)&3&(0,1,2).
\end{array}
\]
In particular neither row has an odd genuine spanning-tree count. The following construction applies to arbitrary \(L_d\), not only these two exact patterns.

## 2. A native switch with freely variable final-prime bits

For any fixed \(L_d\) choose \(m=\dim\ker L_d\) coordinate functionals forming a basis of \((\ker L_d)^*\). Let \(V\) have the corresponding standard basis columns \(e_{p_i}\). Choose fresh distinct helpers \(r_i\equiv1\bmod24\) with the incidence column \(e_{17}+e_{p_i}\) on the marked vertex set. They may be chosen pairwise quadratic residues, and each a quadratic residue at every prime of \(\theta\). These are ordinary coprime CRT conditions, chosen successively; the opposite directions involving a helper are the same by reciprocity. Each helper has exactly two marked neighbors.

Assign \(q_0\equiv7\bmod24\) and let its incidence column on the marked vertices equal the sum of the helper columns. Leave the \(m\) bits \(x_i=[(q_0/r_i)=-1]\) arbitrary. The marked indicator \(\beta\) is in the kernel of the full first-arm \(L\): at marked rows the outside incident sum is zero, at each helper it is two, and at \(q_0\) it is even. Edges between \(17\) and genuine primes vanish because they are \(1\bmod17\). For the native corrected matrix \(L+\lambda a^{\mathsf T}\), \(a=e_{17}+e_{q_0}\) and \(\lambda_p=[(3/p)=-1]\), delete row and column \(q_0\). The correction supplies a \(1\) on the \(17\)-diagonal, and no other correction in the remaining block. The diagonal at each genuine vertex is its original \(L_d\) diagonal because the new incidences to the helpers and \(q_0\) cancel. Eliminating \(17\) thus gives
\[
  \begin{pmatrix}L_d&V\\V^{\mathsf T}&H(x)\end{pmatrix}
\]
for some \(H(x)\). It is invertible for **every** \(x\): pairing \(L_d g+Vh=0\) with \(\ker L_d\) gives \(h=0\) by the chosen coordinate basis, after which \(g\in\ker L_d\) and \(V^{\mathsf T}g=0\) force \(g=0\). Fewer helpers cannot make this bordered matrix invertible (there would remain a nonzero \(g\) in that joint kernel).

With the same fixed helpers, append the whole \(\theta\)-block to the second arm. All old marked diagonals are unchanged by \((\theta/p)=1\), and all other old diagonals are unchanged by the helper square conditions. The extended \(\beta\) still lies in \(\ker L\) by \((\beta/t)=1\). For each fixed \(x\) the old deleted sharp matrix is invertible, so append the \(\theta\)-vertices successively choosing each freely adjustable \((q_0/t)\) to make its Schur complement \(1\). This works for a directed row and column; symmetry is not needed. All final \(q_0\) residue requirements, including \(7\bmod24\), may be imposed simultaneously in a single reduced CRT class. The hypotheses of the original actual finite and all-places Selmer-eight receivers therefore hold for
\[
   n_1=17d q_0\prod_i r_i,\qquad n_2=n_1\theta
\]
with the same literal mark \((\beta,1)\) in the stated coordinates. Empty \(\theta\)-support is allowed. Primes can avoid any finite forbidden set. This is a downstream alteration of the helper/final-prime selection, not a claim about a previously fixed helper set. None of the source primes or the pole is moved; the earlier F–T choices and their local obligations are already fixed.

## 3. The switch extracts exactly the actual fixed bit

Apply the pinned \(\chi_{17}\) reference convolution, with \(B=\operatorname{supp}(d)\sqcup\{r_i\}\). For the first arm let
\[
 F(x)=2^{-|B|-3}\log_2P(n_1)\pmod2 .
\]
It is a multilinear polynomial in the \(x_i\), since its exact terms are
\[
  u(J)\;\det L_{\{q_0\}\cup(B\setminus J)}^{\langle q_0\rangle}.
\]
Here the Laplacian is recomputed on the surviving set, and the superscript means delete row and column \(q_0\). The coefficient of \(x_1\cdots x_m\) only sees terms retaining all helpers. In one such term, choosing each of those variable diagonal entries deletes all the helper rows and columns **without changing the diagonals left on the genuine vertices**. The \(q_0\) and helper incidences cancel by the marked-row condition, so the resulting determinant is the row-sum-zero Laplacian induced on the surviving genuine vertices. It vanishes if any genuine vertex survives. If none survive, it is the empty determinant \(1\). Thus
\[
     \sum_{x\in\mathbf F_2^m}F(x)=[x_1\cdots x_m]F=u(d).
\]
Here \(u(d)\) is the specific \(D=-119d\) weighted reference on the fixed curve \(E_{-17d}\), not the known \(D=-119\) seed. If \(u(d)=1\), at least one of these \(x\) rows gives \(F=1\). Fix that \(x\) and the companion Schur bits for it. **Every prime in the resulting single CRT class** gives a nontorsion first-arm trace, as the convolution depends only on the indicated Legendre bits. Thus the exact first Mordell–Weil mark follows from the existing Selmer-eight plus torsion receiver. No assertion is made about the second Mordell–Weil mark. A conclusion with a further analytic companion assumption is not part of this theorem.

## 4. A single fixed arithmetic datum, without the moving final prime

An alternative unweighted computation of the same bit avoids evaluating any proper-subset reference or requiring marked CM edge orientation. Choose an **independent reference prime** \(q_*\equiv7\bmod24\), \(q_*\nmid17d\), with \((q_*/p)=+1\) for every \(p\mid d\); one such progression exists by CRT. The \(\chi_{17}\) convolution for \(n_*=17dq_*\), with no helpers, has only its all-genuine-deleted term left: every proper deletion leaves \(q_*\) isolated in a graph with a further vertex and has minor zero. Consequently
\[
      u(d)=2^{-9}\log_2 P(n_*)\pmod2 .
\]
The earlier exact full-depth genus theorem now gives the same bit as the ordinary edge phase of a single joint slice for the six positive prime characters of \(d\). Use its reciprocal-\(j\) polynomial \(H\) over \(\mathbf F_2\), keeping one actual slice, not the whole class polynomial. The proved unmarked resultant receiver computes the bit from \(H\); there is no odd residue degree assumption for that receiver. This specifies the missing arithmetic input: an exact \(u(d)\), or just this one exact \(H\) at a reference pair \((d,q_*)\) tied to the fixed original pole. Neither has been produced here. The reference prime can change without changing the bit; promoting or changing the **source** primes changes \(d\) and need not preserve it. The final prime \(q_0\), new helper primes, and all choices involving the companion leave the datum unchanged.

## Exact dependencies and replay

- [Original linear Gaussian source](https://github.com/doublemover/diophantine-z-q/blob/97adcaf7e8331759afbced0339d1a267ac8bf5c4/research/quartic-318-326/actual-linear-denominator-prime-route/original-linear-denominator-prime-route-r1/LINEAR-GAUSSIAN-PRIMES-TO-ORIGINAL-READY-POLES.md), SHA-256 prefix `29e54194`: the actual offsets, Gaussian profile, and order of choices.
- [Normalized \(\chi_{17}\) convolution](../original-detectors-normalized-chi17-convolution-r1/NORMALIZED-ORDINARY-PHASE-AS-CHI17-REFERENCE-CONVOLUTION.md), SHA-256 `b05a0b8e34b24764f3bac1f7c06b18b2b66b53bb7642d27cde8dba5e799e8bb9`; [Feng–Liu–Pan–Tian](https://arxiv.org/pdf/2405.11132), Theorem 2.7 and Proposition 4.2(iii), for its exact Legendre minor.
- `ActualTwoDescentFiniteConclusion318.lean` SHA-256 `0753c3110ab20907e1391cd8dc6682da893c39fccf749be7b8f4c2e35ae409df` and `ActualTwoDescentAllPlacesExactCardinality318.lean` SHA-256 `d67a8a60e7e61be4807eca5397cb8c3236a36b2d5f7100044fed6b3031a29f85`; [companion Schur criterion](../../../rc-native-helper-20261120/ct-original-balanced-detector-selmer-eights-r1/BALANCED-ACTUAL-DETECTOR-SELMER-EIGHTS.md), SHA-256 `4b2d39bf6b4f5e9dda8e33482c723dfba02569f8a0e285c005c646aa35d5fe6e`.
- [Unmarked exact slice receiver](../original-detectors-ordinary-slice-unmarked-resultant-r1/UNMARKED-ORDINARY-GENUS-SLICE-RESULTANT.md), SHA-256 `0656594a6840c53e5f1da36b92c14a9619969d47d3b538f46e33532ff0ecb3e3`.

The byte replay evaluates all the row switches of both exact genuine graphs, checks the top coefficient against **every** possible subset index (not arbitrary guesses for \(u\)), and checks the isolated-\(q_*\) reference filter. It is finite graph arithmetic only.

```
python3 -B verify_universal_first_switch.py | cmp - EXACT-UNIVERSAL-FIRST-SWITCH.json
sha256sum -c SHA256SUMS
```
