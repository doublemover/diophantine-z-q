# Maximal split-level genus depth for the ordinary raw trace

The [original genus-depth calculation](../original-detectors-ordinary-genus-depth-r1/EXACT-ORDINARY-GENUS-DEPTH-AND-NORMALIZED-HEEGNER-BIT.md) used individually \(1\bmod24\) primes and retained 17 and \(q_0\) through the comparison. Both restrictions can be removed. The exact stronger normalization below incorporates composite residue-neutral subsets of either original arm. No normalized value or point on a selected twist is evaluated.

Let \(n>0\) be squarefree with \(n\equiv23\bmod24\). Let \(B\) be its full finite prime support, \(m=|B|\), and define
\[
 V_n=\ker\!\left(\mathbf F_2^B\longrightarrow(\mathbf Z/24)^\times,\quad
      J\longmapsto\prod_{p\in J}p\bmod24\right),\qquad r(n)=\dim V_n .
\]
Here the unit group of order eight is written as a binary vector space. On \(K_n=\mathbf Q(\sqrt{-n})\) use the exact cusp-normalized \(X_0(48)\to E_{-1}\) and raw trace \(P(n)\) from the previous note. For each \(\Delta=\prod_{p\in J}p\) with \(J\in V_n\), use the real genus character \(\chi_\Delta\). The positive \(\Delta\equiv1\bmod24\) and negative \(-n/\Delta\equiv1\bmod24\) are coprime odd fundamental discriminants. The extensions \(K_n(\sqrt\Delta)/K_n\) are unramified at every finite prime by the same local split/unit argument; a nonempty product \(\Delta\) cannot be a square in the imaginary \(K_n\). Thus the \(r(n)\) characters from any basis are independent. Both level ideals have sign plus on this entire group. The squarefree \(n\equiv23\bmod24\) is never an exceptional unit field, nor is the complementary positive \(n/\Delta\) (same residue).

Then
\[
    v_2(\log_2 P(n))\ge r(n)+3 .
\]
For each one of the \(2^{r(n)}\) genuine joint genus slices, its ordinary matched-edge phase is exactly the bit \(\log_2 P(n)/2^{r(n)+3}\bmod2\) after the division. Zero is not a rank test.

**Proof.** Induct on \(m\). If \(r(n)=0\) the local Frobenius telescoping of the full orbit gives the bound 3, whether or not the rational twist trace itself needs a torsion correction. In the general step, let \(J\ne\varnothing\) lie in \(V_n\) and set \(n'=n/\Delta\), \(w=|J|\). Conjugation of the ordinary comparison raw trace gives
\[
     cP(n')=h(K_{n'})T_3-P(n'),
\]
so **\(2P(n')\)** is rational on \(E_{n'}\) even when the class number is odd. The weighted \(R_\Delta(n)\) is already rational on that same twist by the character signs at the level ideals and the Fricke relation. If its height is zero there is nothing to bound. Otherwise [Cai–Shu–Tian, Theorem 1.1](https://arxiv.org/pdf/1408.1733) and Gross–Zagier–Kolyvagin put both nonzero comparison points in rank one, with exactly the same-map constants as before. The free ratio **against \(2P(n')\)** has squared value
\[
     4^{w-1}\,\mathcal L(-\Delta)/\mathcal L(-1).
\]
The real period, local types, and odd winding normalization are unchanged from the previous theorem. The rational torsion comparison for \(\Delta\) with at least two prime factors follows from the two good-to-base ramified inertia primes, whether or not one is 5 or 7; for a singleton \(\Delta\equiv1\bmod24\) those two small good prime reductions still give the previous bound. [Feng–Liu–Pan–Tian, Proposition 2.6(i)](https://arxiv.org/pdf/2405.11132) gives an even integral square when nonzero. Thus the free ratio against \(2P(n')\) has depth at least \(w\). Since the actual local log of \(2P(n')\) is twice that of \(P(n')\), the weighted logarithm is at least \(w+1\) digits deeper than the shorter raw log. There is no loss from needing the torsion correction.

The binary residue rank of the reduced prime support of \(n'\) is at most the old rank, so \(r(n')\ge r(n)-w\). By induction,
\[
 \log_2 R_\Delta(n)\in2^{w+1+r(n')+3}\mathbf Z_2
                        \subseteq2^{r(n)+4}\mathbf Z_2 .
\]
Orthogonality for any of the full genus slices multiplies its sum by \(2^{r(n)}\) and gives \(P(n)\) plus signed weighted terms. Every slice is Frobenius-stable at 2 because every basis character has that local sign plus. Hence its log has depth at least 3, and the deeper weighted bound gives both the stated raw depth and the first normalized residue. This also proves the bound \(r(n)+3\ge\omega(n)\), since the residue rank is at most three.

For the first exact original arm, with all genuine and helper primes \(1\bmod24\), the two exceptional residues \(17,7\bmod24\) are independent so \(r(n)=\omega(n)-2\). The second exact arm has residue rank two or three as soon as it contains the same 17 and \(q_0\); the formula uses its actual remaining residue classes, not a presumed prime factorization of \(\theta\). A neutral helper \(1\bmod24\) increases \(r(n)\) by one, without any new arithmetic premise. Only this maximum among real genus characters splitting at both level primes is meant; other proof techniques could force more divisibility.

