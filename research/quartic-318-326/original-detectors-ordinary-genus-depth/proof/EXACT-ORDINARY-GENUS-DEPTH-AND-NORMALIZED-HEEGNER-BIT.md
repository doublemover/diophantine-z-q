# Exact ordinary genus divisibility and the normalized Heegner bit

For the exact original split-at-2 selector, the previously considered first binary edge phase on a genus half is **identically zero**, not an unknown compatible Frobenius hit. This follows from extra 2-adic divisibility of the full unweighted trace. A different, more deeply normalized bit on a smaller genus slice can certify nonvanishing; its value on the selected production family is not computed.

## 1. Literal family and base lower bound

Let \(n>0\) be squarefree, \(n\equiv23\bmod24\), with the two retained distinct split-selector factors \(17\) and \(q_0\), \(q_0\equiv7\bmod24\). Fix \(k\) other distinct prime factors \(p_i\mid n\), all \(1\bmod24\). Let \(P(n)\) be the unweighted full Hilbert class trace of the literal level-48 modular map \(\phi\) on \(K_n=\mathbf Q(\sqrt{-n})\), at a cyclic level orientation determined by \(\mathfrak p_2^4\mathfrak p_3\). Both level primes split. Locally at a chosen prime over 2, take the connected 2-arm allowed by the exact \(w_{16}\) torsion translation. The completion of the Hilbert class field there is unramified over \(\mathbf Q_2\) and Frobenius acts by the class of \(\mathfrak p_2\), up to simultaneous inverse convention.

On any multiset of these points stable under that Frobenius, the [independently checked ordinary edge identity](../original-detectors-chi17-dyadic-as-edge-phase-r1/FIRST-DYADIC-HEEGNER-BIT-IS-AN-ORDINARY-EDGE-MOMENT.md) gives log divisible by 8. More precisely, the logarithm of the sum divided by 8 modulo 2 is the sum over its reduced actual indexed edges of \((z^2+z)^5=T^{-5}\), with \(z=(t_3-1)^{-1}\) and \(T=(t_3+27)^2/t_3\). That local identity itself works without any rank or Selmer condition. In particular the full trace has \(\log_2P(n)\in8\mathbf Z_2\). The genuine \(D=-119\) control has full log depth exactly 3, so no better universal base bound was assumed.

The primes \(p_i\) give independent unramified quadratic characters \(\chi_i\) of this class group by adjoining \(\sqrt{p_i}\). Indeed, for each positive product \(\Delta\) of the \(p_i\), the two coprime signed discriminants \(\Delta,-n/\Delta\) give the extension \(K_n(\sqrt\Delta)\), unramified at every finite prime of \(K_n\): at odd places use the radicand that is a unit and at 2 both discriminants split. A nonempty such product is not a square in the imaginary quadratic field, proving independence. Every \(\chi_i\) is \(+\) on both \(\mathfrak p_2\) and \(\mathfrak p_3\). Thus each genuine class slice with all \(k\) characters assigned specified signs is nonempty and Frobenius-stable. In particular it is legitimate to use the same local logarithm identity on each slice without dividing by its cardinality.

## 2. Weighted comparison at every omitted subset

For a nonempty subset \(J\subseteq\{1,\ldots,k\}\) write \(\Delta=\prod_{i\in J}p_i\), \(w=|J|\), and \(R_\Delta(n)=\sum \chi_\Delta([\mathfrak a])\phi(x_{\mathfrak a})\) with \(\chi_\Delta=\prod_{i\in J}\chi_i\). As in the [checked height comparison](../original-detectors-dyadic-frobenius-pair-r1/PAIRED-ORIGINAL-DYADIC-BITS-ARE-A-FINITE-FROBENIUS-CONDITION.md), this point and the unweighted comparison \(P(n/\Delta)\) descend to the **same** rational twist \(E_{n/\Delta}\). The weighted conjugation argument is \(\chi_\Delta(\mathfrak p_2^4\mathfrak p_3)=+1\) and \(\phi w_{48}=T_3-\phi\). For the unweighted comparison the class number is even: both 17 and \(q_0\) remain in the odd fundamental discriminant, so the nontrivial unramified factor \(\sqrt{17}\) is still available (genus theory or the same local argument). Thus the translation by the class number times \(T_3\) vanishes. All fields here have only \(\{\pm1\}\) as units and split level primes; the conductor-one hypotheses of [Cai–Shu–Tian, Theorem 1.1](https://arxiv.org/pdf/1408.1733) are exact.

If \(R_\Delta(n)\) is torsion, its logarithm is zero. Otherwise Gross–Zagier and Kolyvagin give rank one on \(E_{n/\Delta}\) and prove \(P(n/\Delta)\) nontorsion. Writing \(m_\Delta,m'\) for the two free coordinates on that same rank-one curve, the same-map height comparison is
\[
 \left(\frac{m_\Delta}{m'}\right)^2
   =\sqrt\Delta\,\frac{L(E_{-\Delta},1)}{L(E_{-1},1)}
   =4^w\,\frac{\mathcal L(-\Delta)}{\mathcal L(-1)} .
\]
Here \(\mathcal L(-1)\) is the odd winding normalization already checked for the literal degree-two map, and [Feng–Liu–Pan–Tian, Proposition 2.6(i)](https://arxiv.org/pdf/2405.11132) makes the nonzero \(\mathcal L(-\Delta)\) an even integral square because \(\Delta>3\) and \(\Delta\equiv1\bmod24\). The old 2 and 3 local types and periods match and \(c_p=4\) at every \(p\mid\Delta\). For \(w=1\), the only variant of the earlier torsion check is to exclude possible \(p\)-power rational torsion at the one new prime \(p\): the good places 5 and 7, which \(p\) cannot equal, have orders 8 or the corresponding quadratic-twist orders 4 and 8 and thus exclude any odd \(p\)-torsion. Inertia at \(p\) kills the rest of odd torsion and forces the rational 2-primary to have exponent at most 2. Hence both curves still have torsion size 4. This proves
\[
 v_2(m_\Delta/m')\ \ge\ w+1 .
\]
In particular the weighted logarithm at the same split 2-place is at least \(w+1\) digits deeper than the **actual unweighted comparison logarithm**, not merely deeper than some free generator. Both twists identify with the same local \(E_0\) over \(\mathbf Q_2\); the two choices of square root can only change the sign. The logarithms are related by the displayed rational free-coordinate ratio because torsion is killed. If the weighted log is zero the divisibility assertion is automatic, even in the torsion case.

## 3. Induction and the exact first possible phase

For every \(k\) as above,
\[
             \log_2P(n)\in 2^{k+3}\mathbf Z_2 .
\]
Prove this by induction on \(k\), the \(k=0\) case being section 1. For each nonempty \(J\), \(n/\Delta\) retains 17, \(q_0\), and \(k-w\) distinguished primes. By induction and section 2,
\[
             \log_2R_\Delta(n)\in 2^{(k-w+3)+(w+1)}\mathbf Z_2
                              =2^{k+4}\mathbf Z_2 .
\]
For the actual all-positive genus slice sum \(A(n)\), character orthogonality on the finite class group gives the **exact elliptic group identity**
\[
 2^k A(n) = P(n)+\sum_{\varnothing\ne J\subseteq\{1,\ldots,k\}}R_{\prod_{i\in J}p_i}(n).
\]
The slice is Frobenius-stable and has log divisible by 8. Apply the logarithm, which is additive on the group, to finish the induction. A different choice of the \(k\) signs gives the same proof with some signs changed on the right-hand weighted terms.

After division, the first potentially nonzero normalized bit is therefore
\[
 \frac{\log_2P(n)}{2^{k+3}}
       \equiv\frac{\log_2 A(n)}8
       \equiv\sum_{[\mathfrak a]\ {\rm in\ one\ joint\ slice}}
                    \overline{T(x_{\mathfrak a})}^{-5}\pmod2 .
\]
The bit is independent of which one genuine slice is chosen. Every previous normalization of the raw logarithm with smaller denominator gives zero, although this says nothing about global torsion. A nonzero normalized bit still implies a nontorsion rational point on \(E_n\); a zero bit is inconclusive about rank.

For an exact intermediate quarter statement, choose the six genuine detector primes in three disjoint pairs with products \(d_a,d_b,d_c\), and use the two independent characters of \(d_a d_b,d_a d_c\). Each of the three nontrivial products has four primes, so its weighted logarithm has depth at least 8 by the preceding weighted comparison (even without counting further distinguished primes in the shorter problem it has depth at least 8). The same orthogonality for this quarter then reads
\(\log_2P(n)/32\equiv\log_2A_{\rm quarter}(n)/8\bmod2\). But the newly proved \(k=6\) depth already implies that this intermediate quarter bit also vanishes. Thus there is no reason to try to evaluate it: the live slice is the one for all usable distinguished primes.

## 4. Exact selector coverage

For each of the original two unbalanced twists (or a balanced split still in the stipulated \(q_0\equiv7\bmod24\) phase), the six actual contact/denominator primes are \(1\bmod408\), hence usable in the theorem. This already gives unconditional \(\log_2P(n)\in512\mathbf Z_2\) on each arm. Old helpers \(1\bmod24\) may also be counted; on an arm with three such helpers in addition to the six, the lower bound is \(2^{12}\), and four give \(2^{13}\). One may count any further distinct factors \(1\bmod24\) on that arm. The exact neutral helper extensions with residue \(1\bmod24\) preserving the marked Selmer eights contribute one extra distinguished prime per helper, independently of their Frobenius images. All these assertions use the same literal source pole and its unchanged \(\beta,\theta\).

In particular the fixed earlier two-phase receiver \(\log_2P/16\bmod2\) is zero for every original prime in the actual row, and remains zero after every such neutral extension. The verified classical Frobenius construction for those fixed bits still identifies the functions correctly, but there is no compatible \(1,1\) word on the actual selector. This new log depth does not determine the new normalized slice moments, any rational rank, or the original PointPair.

