# Exact seventh-moment receiver at the odd ordinary reference

This packet computes the binary phase from **an authenticated reciprocal Weber jet**. It then checks the receiver on two genuine CM discriminants, including both complete positive-genus slices for one nontrivial character. It does not obtain a common-index Gaussian source value, a production slice, the actual bit \(u(d)\), or either rank.

## 1. The endpoint: three coefficients of one true slice

Use the odd-degree isolated reference from the pinned proof. Thus \(D=-17dq_*\) with \(d\) the fixed six-prime support of an actual Ready detector, \(q_*\equiv7\bmod24\) a separate prime split at every \(p\mid d\), and \(f=\operatorname{ord}_{\operatorname{Cl}(\mathbf Q(\sqrt D))}[\wp_2]\) odd. It is **not** the selected shared prime \(q_0\). Fix one complete joint slice for the six positive prime genus characters of \(d\), at a fixed ordinary place over 2.

For each reciprocal \(j\)-invariant \(a\) in this slice, put \(b=a^{1/3}\), the unique cube root over \(\mathbf F_{2^f}\). An equivalent description uses the inverse of the Weber invariant \(\gamma_2\), with \(\gamma_2^3=j\). The characteristic-zero class-invariant choice lies in the CM ring class field since \(3\nmid D\), using a 3-system with \(3\nmid A\) and \(B\equiv0\bmod3\); see Schertz, *Complex Multiplication*, Theorem 6.3.1. At an odd-degree ordinary place its residue has to be this unique branch. No characteristic-zero class-invariant computation is needed for the finite receiver. With \(e_i\in\mathbf F_2\), define the single top jet
\[
    J(Z)=\prod_{b\text{ in the slice}}(1+bZ)
            =1+e_1 Z+\cdots+e_7 Z^7 \pmod{Z^8}.
\]
The true reference bit is \(p_7=\sum b^7\) by the pinned odd-reference theorem: \(a^{2+3^{-1}}\) equals \(b^7\).

In this setting \(e_1=e_3=0\). Here is an independent check of the two vanishings. From the two horizontal 3-neighbors \(x\) of \(a\), each solves \(x^4+ax+a^4=0\). Setting \(x=by\) gives \(y^4+y=b^8\), so \(\operatorname{Tr}_{\mathbf F_{2^f}/\mathbf F_2} b=0\). Alternatively the sum of the two neighbors is \(b\), and summing over a slice closed under both horizontal arrows counts each \(a\) twice.

For \(e_3\), first work on one Frobenius orbit. On the model
\[
    A_a:\quad y^2+xy=x^3+a
\]
of invariant \(j=1/a\), rational order four always exists. The unique geometric order-two point has \(x=0\); the duplication formula \(x(2P)=x(P)^2+a/x(P)^2\) gives \(x_4^4=a\). At \(x_4\), the equation for \(y/x_4\) has right side \(x_4+x_4^2\), of trace zero. Similarly, an order-eight \(x\)-coordinate exists over the residue field exactly when \(V^2+V=x_4^2\) does, with \(V=x^2/x_4\). Such an \(x\)-coordinate gives a rational point: Frobenius could only negate it, and negation contradicts rationality and exact order four of its double. Geometric étale \(2\)-power torsion of an ordinary elliptic curve is cyclic, so \(8\mid\#A_a(\mathbf F_{2^f})\) is equivalent to \(\operatorname{Tr}(a)=0\). Every \(A_a\) here has the same point count: the two generators of the split prime powers of norm \(2^f\) are conjugate, up to sign, in its maximal imaginary quadratic order, and rational order four selects the same sign of trace via \(t\equiv1\bmod4\). The discriminants here are not \(-3,-4\).

Thus \(p_3\) on one Frobenius orbit is the common bit \((\#A_a/4)\bmod2\). In an actual complete slice the number of Frobenius orbits is even. Indeed ordinary canonical lifting is injective on these maximal-order classes, the degree of every orbit is \(f\), and genus theory gives \(2^7\mid h(D)\) because \(D\) has eight prime discriminants. The six independent characters leave \(h(D)/64\) labels, and \(f\) is odd. Therefore \(p_3=0\) globally. From \(J'/J=\sum_{k\ge1}p_k Z^{k-1}\) in characteristic two one gets \(p_1=e_1=0,\ p_3=e_3=0\), also \(p_2=p_4=p_6=0\), then \(p_5=e_5\). The exact endpoint is
\[
                         u(d)=e_7+e_2e_5 .
\]
Only three coefficients of an authenticated true jet suffice. The data still have to describe one whole genus slice, not the whole CM roster, nor an arbitrary subset or a prime-to-2 flag choice.

## 2. The two other cube branches are not a harmless inclusion

If \(P(a)=0\) is a degree-\(f\) reciprocal-\(j\) orbit, then \(P(X^3)\) splits into two factors: its degree-\(f\) inverse-Weber branch and a degree-\(2f\) factor comprising the other two cube roots. For a nontrivial cube root of unity \(\zeta\), the element \(\zeta b\) has exact degree \(2f\): its cube has degree \(f\), and \(2^f\equiv-1\bmod3\) exchanges \(\zeta,\zeta^2\). The two-branch contribution to the seventh power sum equals the degree-\(f\) contribution, since \(\zeta^7+(\zeta^2)^7=1\) in characteristic two. In particular the **three-branch** moment is identically zero, including on a positive genuine control. Finite group-orbit parity cannot recover the correct branch from that total. The replay reconstructs both factors by exact binary polynomial arithmetic, verifies their two traces separately, and checks that the three-branch calculation fails on the positive control.

## 3. Complete exact controls independent of level-3 orientation

The controls use \(D=-119\) and \(D=-22967=-17\cdot193\cdot7\). The latter has one positive genus character of interest and is not in the six-prime source family. The control recovers all relevant reciprocal \(j\)'s by the following finite calculation, not by using an archived class polynomial.

For \(Q=2^f\) a point count on \(A_a\) gives
\[
   \#A_a(\mathbf F_Q)=Q+1+\sum_{v\ne0}(-1)^{\operatorname{Tr}(v^{-1}+av)}.
\]
At \(x=0\) there is one point, and at \(x\ne0\) write the curve equation in \(y/x\) and substitute \(v=x^{-2}\); the trace of \(x\) then becomes the trace of \(v^{-1}\). A binary Walsh transform of the reciprocal trace signs simultaneously gives all the counts, with the explicit trace-dual basis indexing in the script. The polynomial-basis generators cycle through every nonzero residue, so the asserted finite fields require no external irreducibility test. The two cases use
\[
\begin{array}{c|c|c|c|c|c}
D&f&t\equiv1\bmod4&
 \text{field modulus}&t^2-4\cdot2^f&h(D)\\
-119&5&-3&T^5+T^2+1&-119&10\\
-22967&13&-99&T^{13}+T^4+T^3+T+1&-22967&156.
\end{array}
\]
The trace discriminants are fundamental, so maximality is automatic in both enumerated isogeny classes. Conversely the displayed norm relation with odd trace gives a principal \(2^f\) prime power in the CM order; the 2-place Frobenius of every maximal class has degree dividing \(f\). Ordinary canonical lifting keeps these classes distinct. The unique sign of trace in \(A_a\) is the one counted. The replay independently enumerates reduced primitive forms and obtains exactly the stated numbers of distinct observed invariants, with exact orbit degrees \(5,13\) respectively.

The horizontal edges are certified as follows. The two Frob-rational 3-lines are the actual split horizontal branches: modulo 3 the trace vanishes and determinant is \(-1\), giving distinct eigenvalues, and the maximal order splits at 3. Compute both roots of \(y^4+y=b^8\) using
\[
 y=\sum_{i=0}^{(f-1)/2}\sigma^{2i}(b^8),\qquad \sigma:x\longmapsto x^4,
\]
and its translate by 1. This solves the equation because \(1+\sigma\) on the stated sum gives \(1+\operatorname{Tr}_\sigma\) and the right side has trace zero. Horizontal graph closure is verified on all labels. For \(D=-22967\), \(\chi_{193}\) is trivial on the primes over 2 and 3 because \(193\equiv1\bmod24\). Hence every connected component under Frobenius and both horizontal moves is contained in a true genus slice. There are exactly two components, both size 78; the nontrivial genus character has two fibers of size 78. These components are precisely the **two whole true slices**, without requiring a possibly false identification of their signs by the least residue representative.

For \(D=-119\) the true zero-character slice has degree ten. Its two exact reciprocal-\(j\) factors, in binary polynomial bit-mask notation, are 59 and 61. The inverse-Weber factors are 47 and 37; the remaining branch factors are 1291 and 1077. In particular the exact hand multiplication of the two reciprocal reversed factors gives
\[
 (1+Z^2+Z^3+Z^4+Z^5)(1+Z^3+Z^5)
 \equiv 1+Z^2+Z^4+Z^5+Z^6\pmod{Z^8}.
\]
Thus \(p_7=1\), independently agreeing with the previously calibrated genuine \(D=-119\) reference. The two degree-5 orbits have respectively \(1,0\), so both branches cannot be added blindly.

For both \(D=-22967\) slices the exact jet is \(1+Z^2+Z^4+Z^6\), giving \(p_7=0\) on each. Their orbit traces are \((1,0,1,1,1,0)\) and \((1,1,0,1,1,0)\) in the fixed file order; this is a real parity cancellation, not a roster with all local terms zero. The JSON states every irreducible orbit factor and the exact leading jet. A separate edge sum \(\sum_{\{a,a'\}}(a+a')^5\) over the actual unordered horizontal edges agrees with the Newton and orbit-trace calculations in each slice. None of these controls evaluates an actual six-prime reference.

## 4. Streaming evaluator and stop boundary

The executable `weber_seventh_moment.py` accepts either one JSON array of eight entries \([1,e_1,\ldots,e_7]\) per authenticated factor, or one monic binary polynomial bit-mask per line with `--polynomials`. It multiplies truncated jets, uses Newton's identities, and returns the phase. The verifier does not claim that arbitrary inputs are sourced from CM, are the correct branch, or form an entire slice. Aggregation uses only eight accumulator bits and at most 36 binary term products per factor, independent of the factor degree when the jet is already supplied. If the complete aggregate jet is known, only \(e_2,e_5,e_7\) are needed.

The field scan is **not** the implementation for the real source. A principal split-2 power must satisfy \(t^2+|D|v^2=4\cdot2^f\) with \(v\ne0\): a rational generator would give both conjugate valuation arms, not the one prime power. Therefore \(2^f\ge |D|/4\), regardless of the selected odd residue degree. The WHT uses at least \(2^f\) entries and \(O(f2^f)\) operations. Even abandoning all other exact Gaussian ray conditions, six genuine primes \(1\bmod408\) are each at least \(409\), so \(|D|/4\ge(119/4)409^6>10^{17}\) for the literal reference. This rules out extending this *control constructor* as a full-field scan of the actual data; it is not an algorithm lower bound for class invariants or for the seventh moment itself. Streaming avoids storing a large slice polynomial but does not create its factor jets or prove a sublinear computation of them.

Current stop condition: neither a genuine six-prime source roster for an actual common-index pole nor the authenticated Weber jet for such a roster is supplied here. A conservative next implementation would seek the three coefficients from CM reciprocity or a relative trace computation without traversing the full slice. Do not use these control timings to project production feasibility.

## Dependencies and replay

- [Odd degree on the isolated reference](../original-detectors-isolated-reference-odd-residue-degree-r1/ODD-DEGREE-ON-ISOLATED-PRIME-REFERENCE.md), SHA-256 d9867f789b2d77800353e5f0c0d3389c161fb3b94264458c1bf50b98281c7549.
- [Earlier canonical-lift and unmarked slice proof](../original-detectors-ordinary-slice-unmarked-resultant-r1/UNMARKED-ORDINARY-GENUS-SLICE-RESULTANT.md), SHA-256 0656594a6840c53e5f1da36b92c14a9619969d47d3b538f46e33532ff0ecb3e3.
- [Exact prior \(D=-119\) calibration](../original-detectors-chi17-tame-dyadic-jet-r1/ONE-TAME-ORDINARY-JET-FOR-THE-ACTUAL-DYADIC-LOG.md), paper SHA-256 prefix fa703237.
- [Schertz, *Complex Multiplication*, §6.3](https://www.cambridge.org/core/books/complex-multiplication/), Theorem 6.3.1. The finite branch construction in this packet does not require this characteristic-zero interpretation.

```
python3 -B replay_ordinary_seventh_moment.py | cmp - EXACT-ORDINARY-SEVENTH-MOMENT.json
printf '47\n37\n' | python3 -B weber_seventh_moment.py --polynomials
sha256sum -c SHA256SUMS
```
