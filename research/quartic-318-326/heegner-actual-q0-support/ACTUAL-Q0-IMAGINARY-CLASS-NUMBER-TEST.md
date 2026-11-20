# The exact q₀ test needs only imaginary quadratic 4-rank

This supersedes the more expensive real-dyadic ray implementation of the same arithmetic test (0e8bdd66…, f27a6da6…). For the fixed compact scalar δ=1−b/17>0, let its exact positive squarefree class be θ, `θ≡1 mod24`, and fix valid earlier I slots. Take any trial prime q of type 7 mod12, unramified for θ and satisfying all old-row conditions (β, I, and separately any detector residue and common-CM-field splitting). Then with the exact same literal companion block H(q) of the original deleted K♯, one has
```
nullity H(q) = r₄ Cl(Q(√(−qδ))) = r₄ Cl(Q(√(−qθ))).
```
No field changes are made to the actual Heegner constructions. This imaginary quadratic field is a **test object**, not the positive field used to select I or the compact common CM field for the trace. Here r₄ of a finite abelian class group C is dim_F₂(C[2] ∩ 2C). In particular, q passes the exact companion arithmetic incidence test iff the 2-primary class group of this test object is elementary abelian. Computing it for the compact scalar is still undone. The test does not include any analytic nonvanishing.

## 1. Identify the actual unsigned block, with signs adjointed correctly

Let S consist of all primes of θ and q. The fundamental discriminant of L=Q(√(−qθ)) is the odd D=−qθ, since q≡3 mod4, θ≡1 mod4, and q∤θ. Thus D=∏_{p∈S}p*, where p*=(-1)^{s_p}p for s_p=[−1/p]. In particular Σs_p=1 in F₂. There is **no prime 2 row**.

Let the full unsigned matrix U have rows p, columns r, off-diagonal U_pr=[r/p], diagonal U_pp=Σ_{r≠p}[r/p]. The orientation of [Stevenhagen, Theorem 3.1 and formula (16)](https://doi.org/10.1017/S0305004121000335) is that the Rédei character-row p is the genus character for p*, and the column r is the class of the prime ideal over r. For different odd p,r the entry satisfies
```
[p*/r] = [p/r]+s_p s_r = [r/p].
```
The diagonal in this orientation is determined by **column** sums: the product of all genus characters is trivial. This diagonal equals the unsigned **row**-sum diagonal, because the difference at column p is
```
Σ_{r≠p} ([r/p] + [p/r]) = s_p(1+s_p)=0.
```
Thus U is the exact matrix in formula (16), not an unsigned proxy. It has zero row sums and zero column sums. Delete the row and column for q. This gives exactly H(q): its diagonal at p is [θ/p at p]+[q/p], and all remaining off-diagonals are unchanged. Rank is preserved by this deletion: replace the q row by the sum of all rows and the q column by the sum of all columns (invertible row/column operations), leaving H intact and making the added row/column zero. With t=|S|, the 4-rank formula r₄=t−1−rank U now gives the asserted nullity identity.

## 2. Cross-check against the literal norm obstruction

For a kernel divisor d|θ, the earlier rational conic equivalently makes qθ/d a norm from Q(√d), i.e. (d,qθ/d) is the trivial quaternion class. The identity (d,d)=(d,−1) of Hilbert symbols gives (d,qθ/d)=(d,−qθ). By symmetry and the norm theorem this means d is a norm from the **imaginary** L, exactly as above.

If P_d is the product of the ramified prime ideals of L above the primes dividing d, [P_d] is square in the class group iff d is a rational norm from L. Indeed if (α)=P_d A⁻², then Nm(α)·Nm(A)²=d (positive norm in the imaginary field). Conversely if Nm(α)=d, then (α) has parity d at all ramifying primes. For a split odd pair or split dyadic pair outside d the valuations have even sum, so both parities can be made even by a rational principal factor. At an inert prime a rational principal factor makes its ideal valuation even as well. This turns (α) into P_d times a square fractional ideal, modulo principal rational factors. There are finitely many required parity corrections. Finally the ramified ideals generate Cl(L)[2] with the sole relation the product over S (odd negative fundamental D with t≥1 here, and D<−4 in the production case); excluding q removes that relation. This gives the same identification, with a norm explanation of why the real-field dyadic obstruction disappears. The matrix proof also covers the vacuous θ=1 and q=7 case.

## 3. Effective search target and actual compact-data boundaries

If a class-number computation is cheaper than a presentation of the class group, one can use
```
q passes  ↔  v₂ h(Q(√(−qδ))) = ω(θ)
           = 1 + r₂ Cl⁺(Q(√δ))    (when θ>1).
```
Indeed imaginary genus theory gives r₂ Cl(L)=|S|−1=ω(θ), and equality of the 2-order with that rank is equivalent to exponent at most 2. The rightmost fixed constant can be obtained once from the real narrow class group by genus theory; this requires no list of θ factors, and then each trial needs only the ordinary imaginary class number. One may instead test the 2-primary invariant factors directly. These are **exact finite algorithmic tests** with the same field prescriptions. By scanning primes in the exact old-row CRT ray, excluding those dividing the numerator or denominator of δ, and testing this condition, the arithmetic search must terminate by the original independent diagonal selection and CRT proof. A retained known four-bit prefix can be included directly, using the same determinant-preserving Schur completion as before. The additional q conditions at 53 or at the compact common-field numerator are independent of the unknown θ rows, as already checked.

An actual implementation must still compute and certify the maximal-order arithmetic of these actual fields. It is not valid to use the class number of a nonmaximal order with discriminant −q times an arbitrary positive representative of the class of δ. Algorithms may internally factor integers or require their full expansion. The improvement is that the support factor list disappears as a supplied selector input, and all relative real-ray maps disappear from the decision criterion. There is no complexity or practicality claim for the literal large circuit.

For θ=145, the prior q=7 real-field diagnostic had ordinary **real** narrow 4-rank zero but H singular. The correct field is imaginary: h(−1015)=16 and ω(145)=2, so it rejects. At q=43 the earlier H passed; h(−6235)=12 gives v₂=2, so it passes. The exact accompanying Python script enumerates primitive reduced positive definite forms (including the correct sign at a tie), reproduces both class numbers, and checks the signed Rédei/deleted rank on both specimens.

No conclusion about A₋(n), A₋(nθ), A₊(mn), or A₊(mnθ) follows from this arithmetic test, and no numerical q on the fixed production scalar has yet been certified. It changes only the q arithmetic gate.
