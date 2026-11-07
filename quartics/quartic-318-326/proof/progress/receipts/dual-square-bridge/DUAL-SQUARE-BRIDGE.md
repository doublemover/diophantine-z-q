# Actual dual square-abscissa bridge

This packet works with the project's exact field K = Q(sqrt(2)), D = (3 - sqrt(2))^2, and actual Mathlib elliptic-curve points. It does not assume a class-number theorem, a ring-of-integers identification, a prime-place coverage theorem, or a unit-classification theorem.

## Main results

- `GlobalHeightPositivity318.canonical_R_positive`: the existing `CanonicalData` inequalities already imply positive canonical height of the actual point R. The former separate positivity premise is redundant.
- `GlobalDualSquare318.dual_square_abscissa`: the exact `GlobalSquareHalving318.DualSquareAbscissa` proposition.
- `GlobalDualSquare318.square_halving`: actual square-abscissa source points have actual group halves, with no dual-descent premise.

## Proof route

1. `DualLocalArithmetic318` proves positivity of a nonzero dual abscissa at both real embeddings, and the odd-minimum valuation obstruction.
2. `DualSeven318` and `DualSignature318` separately verify parity at the previously constructed normalized split, inert, and ramified dyadic places. These provide a concrete local signature; the final global proof does not assume that these places exhaust all prime ideals.
3. `PositiveUnitSquare318` uses Mathlib's proved Pell theorem. The fundamental norm-one solution is (3,2) = (1 + sqrt(2))^2. Positive first coordinate excludes the negative branch. Hence every totally positive actual unit of Z[sqrt(2)] is a square in K.
4. `EuclideanSqrtTwo318` constructs the actual Euclidean-domain instance on Z[sqrt(2)]. Rounding both coefficients of a field quotient to nearest integers gives absolute field norm at most 1/2. The Euclidean measure is the absolute integer norm.
5. `FractionSqrtTwo318` constructs the injective ring map to K, clears rational denominators, proves K is its fraction field, and extends each prime's multiplicity valuation to K. The extension is exactly multiplicity on nonzero integral elements. Reduced fractions of valuation zero have numerator and denominator both prime to that prime.
6. `DeltaPrime318` defines reduction a + b sqrt(2) to a + 3b in F7. Its kernel is exactly divisibility by delta = 3 - sqrt(2), proved by an explicit quotient. Thus delta is prime. F7 anisotropy of a^2 + 4b^2, combined with reduced fractions, rules out the exceptional odd abscissa value one at delta.
7. `DualPrimeParity318` proves even abscissa value at every actual prime-multiplicity valuation. Away from delta, the coefficient 4D has value divisible by four because 2 = (sqrt(2))^2. At a prime dividing delta, association with the proved prime delta reduces to the preceding residue argument.
8. `SquareFactorization318` uses normalized prime factors to write an integral element with even multiplicities as a square times a unit. A reduced fraction with every prime value even has even numerator and denominator multiplicities. The quotient unit is totally positive, hence is an actual square by step 3.
9. `GlobalDualSquare318` composes these results into the exact dual assertion and the already-proved actual group-halving theorem.

## Scope

This closes the dual square-abscissa arithmetic and canonical-height positivity premises. It does not claim the full global generator theorem: the first descent squareclass coverage, global canonical-height construction/comparison, finite height-box coverage, and any remaining wrapper obligations are separate.

The Euclidean and fraction-field modules are intended for direct reuse in the first-descent eight-squareclass calculation. No repository files were changed, and no PR was opened.

## Verification

Run `bash run.sh` from this folder or `bash dual-square-bridge/run.sh` from its parent. Every module is compiled with kernel checking enabled. `DualAudit318.lean` recursively audits every declaration originating in all eleven packet modules and rejects any axiom except `propext`, `Classical.choice`, and `Quot.sound`. The final receipt records the result and exact source hashes.
