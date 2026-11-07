# Actual canonical height: formal closure

## Exact result

`ActualCanonicalHeight318.canonical_data` proves

`GlobalSaturationHeight318.CanonicalData ActualCanonicalHeight318.canonicalHeight`.

There are **no theorem parameters**. The final axiom audit reports only `propext`, `Classical.choice`, and `Quot.sound`. In particular, neither a detached height model, a canonical-height existence assumption, a parallelogram hypothesis, nor an unproved field-normalization fact is retained.

`canonicalHeight P` is one half of the actual limit of

`(1/4)^n * GlobalSaturationHeight318.xHeight ((2^n : Nat) • P)`.

`ActualCanonicalHeight318.canonical_tendsto` proves convergence to this definition. `xHeight` is the live `NumberField.absLogHeight₁ (P.xRep 0)`.

## Construction

**CanonicalLimit.lean** works for any abelian group and any real height with nonnegative defect constants L,U satisfying

`4*h(P)−L ≤ h(2P) ≤ 4*h(P)+U`.

Its consecutive normalized terms differ by at most `max(L,U)/4 * (1/4)^n`, so Mathlib's complete-space Cauchy theorem supplies the genuine limit. An induction retains the separate geometric bounds

`h(P)−L/3*(1−(1/4)^n) ≤ seq(n) ≤ h(P)+U/3*(1−(1/4)^n)`.

Passing to the limit gives exactly `h(P)−L/3 ≤ raw(P) ≤ h(P)+U/3`. Nonnegativity and zero follow from the actual sequence. Shifting the convergent sequence proves `raw(2P)=4*raw(P)`. Since doubling kills an actual 2-torsion point, this also proves 2-torsion invariance.

**CanonicalQuadratic.lean** scales an approximate parallelogram defect by `(1/4)^n`; its bound tends to zero. Uniqueness of limits gives the exact parallelogram law for `raw`. Two-step induction proves the natural-number square law, and the parallelogram law at zero gives evenness and therefore the integer square law. No quadraticity is assumed of the input height.

**ActualCanonicalHeight318.lean** supplies the arithmetic inputs:

- `GlobalDuplicationHeight318.absolute_duplication_bounds`, already kernel-proved in the live height lane, gives the actual constants `L=log392` and `U=log676`.
- Mathlib's `WeierstrassCurve.Affine.approx_parallelogram_law` applies to the actual E over K=Q(sqrt(2)). Its ellipticity is derived from the already-proved nonzero discriminant. The naïve height is exactly twice the actual absolute x-height, by the proved normalization interface, so this is an actual bounded parallelogram defect for `xHeight`.
- `BasePointHeight318.heightP` supplies the actual `xHeight(P)=log41`.

Every field of the live `CanonicalData` is then filled, including zero, nonnegativity, integer quadraticity, 2-torsion invariance, both asymmetric comparisons, and base height.

## Reproduction and scope

Run `bash verify.sh` in this directory. It uses the existing project-local toolchain, enables kernel type checking explicitly, and rejects any axiom output containing `sorryAx`. The receipt binds all module sources, objects and axiom logs, plus the exact consumed arithmetic inputs.

This closes the canonical-height interface. It does not by itself prove a Mordell–Weil rank bound, a full generator theorem, or remove the global `sourceArithmetic` hypothesis. No live height source or repository source was edited by this package.
