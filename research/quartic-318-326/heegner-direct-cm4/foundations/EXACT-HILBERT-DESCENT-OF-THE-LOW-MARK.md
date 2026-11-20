# Exact descent of the conductor-four low mark to the Hilbert class field

This is an addendum to the exact level-48 CM4 trace argument (proof `2783a2a3…`, manifest `9ed66e14…`). It improves the arithmetic field and character scope of its partial trace. It does not prove that the full trace in the fixed selected family is nontorsion.

Use the same d≡11 mod24, A=E₋₁, pointed map f:X₀(48)→A, cyclic conductor-four point P and ring class H₄. Let H be the Hilbert class field. The relative kernel C4→C of their class groups is cyclic order six, represented by the local units at 2: ω of order three and u=1+2ω of order two in the quotient. This exact kernel is O_{K,2}ˣ/O_{4,2}ˣ, with no extra global-unit quotient since O_Kˣ={±1} is already in O₄ˣ.

## 1. The order-two local action is invisible on the actual pointed map

Let a=S₂=([[1,1/2],[0,1]]) act by z↦z+1/2 on X₀(48), and w=W₄₈=[[0,−1],[48,0]]. The matrix a normalizes Γ₀(48): conjugating [[A,B],[48C,D]] gives top right B+(D−A)/2−12C integral since A,D are odd, and bottom left still 48C. The same holds for w a w⁻¹. The weight-two newform of A has no even coefficients (its level has exponent 4 at 2 and its local Euler factor is 1). Thus a changes the differential by −1. Since it fixes the base cusp ∞, the equality of pointed elliptic maps is **f∘a=−f**. Also f∘w=−f+T with T=(3,0) and 2T=0. It follows, on actual points, that
```
f∘(w a w⁻¹)=−f,  and  f∘γ=f for γ=a(w a w⁻¹).
```
In particular no torsion correction has to be discarded in the second identity.

For the local centered coordinates of the previous note use g₂=diag(4,1). The exact rational matrix γ=[[−11,1/2],[−24,1]] gives g₂γg₂⁻¹=[[−11,2],[−6,1]], congruent to [[1,2],[2,1]] mod4. This is uδ₂ modulo4, with δ₂=diag(1,−1) in the centered level subgroup. Away from 2 the matrix γ is integral of determinant 1 and its lower left entry is divisible by 3, so it lies in the stipulated level subgroup there. The finite idèle equal to u at 2 and 1 elsewhere therefore has the **same level coset** as this rational normalizer in the original coordinates; changing the direction of its adelic action only uses γ⁻¹, also fixing f. Consequently f(P_a) is fixed by the relative order-two class u on every indexed CM point. This is stronger than the local representation's +1 result, and requires the based cusp translation and a_even=0.

## 2. A literal trace from the maximal class orbit

Let U₃ be the order-three subgroup of the relative kernel. For each a∈C, choose any lift ã in C4 and define
```
X_a = Σ_{κ∈U₃} f(P_{ãκ}).
```
It is independent of the lift, since the κ choices permute summands and u leaves f unchanged. The class action is genuine: σ_g(X_a)=X_{ga}, and all X_a lie in A(H). This is a finite sum of the actual cyclic marks, not division of a ring-class sum by an unproved power of two. Summing over C gives a point X∈A(K) and the full H₄ trace is exactly [2]X because each relative coset duplicates the three used values. In particular the two full traces are nontorsion simultaneously.

The prior exact Fricke-cc relation descends to
```
cc(X_a)=−X_{b a⁻¹}+T,
```
where b is the marked ordinary ideal class of the same prime over 3 or inverse. The factor 3 on T from the three terms is 1 on this order-two point. For any odd-order subgroup V≤C, put X_V=Σ_{a∈V}X_a. With ρ=σ_{b⁻¹}cc, one has X_V+ρ(X_V)=T. Since H/Q is unramified at 2,3, it contains none of i, √3, √−3, so none of the three nonzero rational 2-torsion points are halved in H. Thus the 2-primary torsion of A(H) is exactly A[2], fixed pointwise; id+ρ cannot take any torsion point to T. Therefore X_V is nontorsion.

For the largest odd V this locates a nonzero component at a character of **2-power order of the true maximal class group C**, not just of Pic(O₄). This conclusion can be read directly by decomposing the finite group action on A(H)⊗C. It still need not pick the trivial character. On the selected arithmetic gate |2C| is even, hence the above odd-degree obstruction does not apply to the trace from the usual genus field to K.

## 3. Exact first obstruction to importing the old compatible induction

For E_d, let −d=(−r)s be the signed fundamental factorization of a genus character, r,s>0. Necessarily s≡1 mod4 and r≡3 mod4; d≡11 mod24 and 3∤d give the four rows below. The pair of ordinary constituents for the base A=E₋₁ is E_r and E_{−s}:

| s mod24 | r mod24 | root of E_r | root of E_{−s} |
|---:|---:|:---:|:---:|
| 1 | 11 | − | + |
| 5 | 7 | + | − |
| 13 | 23 | − | + |
| 17 | 19 | + | − |

These root values are the exact list in [He–Hu–Tian, introduction](https://www.sciengine.com/doi/pdf/C674839BE2234E14B7ACCE693F245CF6), not a claim of analytic nonvanishing for any error term. In the actual one-I family 5 divides β, so s=5 is genuinely available as a proper positive prime discriminant; proper contributions are **not** restricted to the smaller positive 11- or 23-type derivative family. Also the dyadic class character at 2 is trivial for every genus character here (unramified on K₂ and trivial on the rational uniformizer 2), so the specific local test above does not suppress these extra signs. A proof of the original selected endpoint by projecting the direct Hilbert trace needs an exact integral comparison that handles these contributions; the already available ±1 mod24 factor induction does not do so.

No evaluation of the full actual H trace, actual companion point completion or paired nonvanishing follows. The exact gain is removing the dyadic relative kernel from the **global arithmetic point** and isolating the remaining ordinary genus-character issue.
