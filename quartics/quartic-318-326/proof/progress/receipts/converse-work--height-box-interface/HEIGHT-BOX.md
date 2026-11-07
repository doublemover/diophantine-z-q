# Actual absolute-height coefficient box: formal closure

Source: pinned V10 `quartics/quartic-318-326/docs/sources/quartic_v10.tex`, the small-height paragraph around lines 377–399. The live interface is `../../height-work/PolynomialHeightInterface318.lean`; its `xHeight` is exactly `NumberField.absLogHeight₁ (Q.xRep 0)`.

## Result

`PrimitiveQuadraticMahler318.polynomial_height_coverage` proves the live `PolynomialHeightCoverage` with **no hypothesis**. In particular, the earlier remaining `PrimitiveHeightIdentity` is now proved by `PrimitiveQuadraticMahler318.primitive_height_identity`. There is no replacement model height, unproved field-invariance assumption, custom axiom, or admitted theorem.

`BasePointHeight318.heightP` additionally proves the exact base-point height `xHeight P = Real.log 41` used in `CanonicalData.heightP`.

Thirteen isolated modules audit 59 declarations with only `propext`, `Classical.choice`, and `Quot.sound`. `verify.sh` rebuilds every module with kernel checking enabled; `receipt.json` binds the sources, compiled objects and axiom outputs. No live height files or repository files were edited. Scratch API-query files are not part of the certificate.

## Proof chain

1. **RationalAbsoluteHeight** proves the rational absolute-height formula in any characteristic-zero field. It unfolds the actual simple-subfield definition. In any number field, Bezout makes the local primitive numerator/denominator maximum one at every finite place, while infinite multiplicities sum to the field degree. Taking the actual degree root gives `log(max(|num q|,den q))`.

2. **RationalPointBox318** proves the actual rational elliptic-point box and reduces coverage to the genuinely nonrational branch.

3. **QuadraticDiscriminant318** proves the discriminant shape from an actual root in Q(sqrt(2)). If twice a rational square is integral, the rational denominator square divides two, so the denominator is one. The discriminant is therefore `2*k^2` for a positive integer k.

4. **PrimitiveQuadratic318** clears the two actual rational denominators, divides the coefficient triple by its actual gcd, and constructs a positive-leading primitive integer quadratic with the actual root.

5. **QuadraticHeightBounds** applies Mathlib's complex Mahler coefficient bound. A quadratic of Mahler measure below81 has coefficient bounds81,162,81. Those bounds and the proved discriminant identity give `k≤162`.

6. **HeightCoverageFromMahler318** assembles the exact live coverage from the height identity. The identity is only a parameter in this intermediate module; it is discharged in step12, not assumed by the final theorem.

7. **LocalMahlerHeight** proves primitive polynomial Gauss norm one at every actual normalized `NumberField.FinitePlace`. Gauss multiplicativity then gives

   `w(a) * max(w(x),1) * max(w(x'),1) = 1`.

8. **FiniteHeightEquiv** proves invariance of the actual finite-place height product under any number-field ring equivalence. It does not assume a place-permutation theorem. A normalized denominator n is obtained from Mathlib's integral ideal construction. Ideal norm is preserved through a quotient ring equivalence. The ideal-norm/product formula gives the finite height product exactly n, in both isomorphic fields.

9. **RelativeHeightEquiv** expresses the archimedean product as a product over all complex embeddings, then transports it by precomposition with a field equivalence. Combining step8 proves relative multiplicative-height invariance under any number-field ring equivalence.

10. **ActualQuadraticEmbeddings318** classifies every actual complex embedding of K=Q(sqrt(2)) as the positive or negative real embedding. Every actual infinite place is real. The actual infinite height product at u+v sqrt(2) is precisely

    `max(|u+v sqrt(2)|,1) * max(|u-v sqrt(2)|,1)`.

11. **AbsoluteHeightNormalization318** proves that Q(u+v sqrt(2))=K when v is nonzero. Step9 transports relative height from the actual simple subfield in the absolute-height definition. The degree is exactly two. Together with step1 this proves for **all** x in K, including rationals,

    `absLogHeight₁(x) = log(mulHeight₁(x))/2`.

12. **PrimitiveQuadraticMahler318** obtains the actual two-root factorization from the real and imaginary coefficient equations. Conjugation invariance from step8 and the product formula for a imply the finite height product is exactly a. Steps10 and11 and the literal Mahler factorization prove

    `M(p) = mulHeight₁(x) = exp(2*absLogHeight₁(x))`.

    The intermediate coverage theorem then supplies `PolynomialHeightCoverage` without an argument.

13. **BasePointHeight318** checks the primitive polynomial `64*X²−912*X+1681` for the actual `xP=57/8−(7/2)sqrt(2)`. Both real conjugates exceed one. The actual relative height is1681, so the absolute logarithmic height is `log41`. The theorem is wired to the actual elliptic `P` and `xRep`.

## Reusable exact interfaces

- `ActualQuadraticEmbeddings318.every_infinite_place_real`
- `ActualQuadraticEmbeddings318.infinite_place_real_value`
- `ActualQuadraticEmbeddings318.infinite_part_pair`
- `FiniteHeightEquiv.finite_part_equiv`
- `RelativeHeightEquiv.mulHeight_equiv`
- `AbsoluteHeightNormalization318.absLogHeight_eq_half_relative`
- `PrimitiveQuadraticMahler318.primitive_height_identity`
- `PrimitiveQuadraticMahler318.polynomial_height_coverage`
- `BasePointHeight318.heightP`

## Scope

The coefficient-box and concrete base-height inputs are now formally closed. This does not itself prove the canonical-height construction, rank/saturation, or the full generator theorem. The finite candidate enumeration and the remaining global generator work belong to the live height lane. No claim is made that the complete restricted-converse arithmetic has been formalized or that the global `sourceArithmetic` hypothesis has been removed.
