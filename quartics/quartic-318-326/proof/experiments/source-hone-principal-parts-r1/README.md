# Bounded principal parts for the original infinity denominator

This is an uncompiled two-source continuation, with baseline-only dependencies.
No local Lean check, axiom audit, independent acceptance or H1 dimension/spanning
result is claimed. Hosted strict checking and recursive audit remain pending.

`PolynomialPrincipalParts318` proves the exact polynomial decomposition

P = R D^m + S X^n, with degree R < n,

when D(0) is nonzero, for every n and m including zero. The proof derives
coprimality of X and D, uses Bezout for their powers, and reduces the principal
numerator by monic division by X^n. It does not assume a bound on the original
numerator or silently exclude the polynomial-zero case.

`ContactInfinityPrincipalParts318` instantiates D with the **original**
`InfinityOpenChart318.denominator c`. The nonvanishing at zero is the existing
actual-chart theorem. It evaluates the polynomial identity at the **original**
coordinate `InfinityFieldCoordinates318.u c` in the **original** contact function
field and proves the exact partial-fraction identity

P(u)/(u^n D(u)^m) = R(u)/u^n + S(u)/D(u)^m.

Nonzero denominators follow from the already constructed transcendental u map
and the original chart denominator, not from an extra generic-point assumption.
The finite remainder has degree below n, while the second fraction has only the
original localization denominator, which is nonzero at infinity.

This removes the infinity-regular denominator from a proposed principal-part
calculation. It does **not** yet prove that every actual overlap coefficient has
been represented by such a fraction, transport the regular fraction back to an
explicit infinity-ring element, eliminate the finite-chart image, or prove that
only the expected five H1 classes remain. Those are distinct next consumers.

The producer inspected the pinned polynomial division and coprime-power APIs at
Mathlib commit `56a005855ea17e0b0958f73ec801ae140b0a1679`. Strict-module elaboration,
polynomial degree coercions and field-simplification normalization are still
subject to CI. No old packet, receipt or accepted manifest is changed.
