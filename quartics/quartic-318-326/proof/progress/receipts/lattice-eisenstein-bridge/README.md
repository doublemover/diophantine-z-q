# Actual lattice, Eisenstein and Weierstrass point binding

This packet closes the actual lattice-invariant normalization seam, using genuine Mathlib lattices, sums, Eisenstein series, Weierstrass functions and elliptic points. It does not assume a lattice/modular invariant equality or a torus j equality.

## Actual lattice and sums

`PeriodEisenstein318.periods tau` is the genuine PeriodPair with periods tau and one. Its real-linear independence is proved from Im(tau)>0. `latticeEquiv` constructs an explicit bijection from Z² to the actual lattice, v -> v0*tau+v1. Injectivity uses the imaginary part and surjectivity uses actual span membership.

`G_eq_eisenstein_sum` reindexes the actual lattice sum through that bijection. `G_norm_summable` establishes absolute convergence for n>=3. Mathlib's actual lattice-summand/zeta identity then gives `G_eq_normalized`:

    G_n(tau) = 2 zeta(n) E_n(tau).

The factor two is retained because Mathlib's normalized E divides the primitive signed-pair sum by two.

## Exact invariant normalization

`LatticeInvariants318` evaluates the necessary zeta constants, including zeta(6) from the proved Bernoulli formula. It gives

    G4 = pi^4 E4 / 45,
    G6 = 2 pi^6 E6 / 945,
    g2 = (4/3) pi^4 E4,
    g3 = (8/27) pi^6 E6.

The actual normalized coordinate functions are

    x(z)=wp(z)/(2 pi)^2,
    y(z)=wp'(z)/(2(2 pi)^3).

The genuine Mathlib Weierstrass differential equation implies the exact cubic with coefficients -E4/48 and -E6/864. The factors two and pi and the c6 sign are checked algebraically; no analytic normalization is supplied as a hypothesis.

## Actual elliptic point and quotient function

`LatticeModelPoint318.actual_equation` identifies the displayed cubic with the actual `WeierstrassCurve.Affine.Equation` of `ModularWeierstrass318.curve tau`. Its already-proved nonzero discriminant makes the actual affine points nonsingular. The packet constructs actual elliptic points away from the lattice and assigns lattice arguments to the actual point at infinity.

The genuine periodicity of wp and wp' proves `point_add_period`. Therefore `torusPoint` is a genuine function from the actual quotient C/(Z*tau+Z) to the actual elliptic Point type, with the stated representative formula. The model's actual algebraic j was already proved equal to the actual modular j in modular-weierstrass-bridge.

## Exact remaining scope

No bijectivity, additive-homomorphism property, analytic isomorphism or global uniformization theorem for `torusPoint` is claimed. Identification of a specified modular-curve fiber with this model also remains a geometric/moduli application. The actual lattice-invariant normalization and actual point/period descent are now proved; those remaining claims must not be conflated with them.

## Replay

Run `bash run.sh` for a strict rebuild and full recursive standard-axiom audit. The receipt records all source/dependency hashes and the exact declaration count. Twenty missing official cache files for Mathlib's actual Weierstrass analytic library were obtained from the official Mathlib cache. No repository or Git operation was performed.
