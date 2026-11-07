# Global differential energy to the actual cusp/Jacobian data

Strict kernel PASS: two modules, four public theorems and one constructed Data-to-cusp map. The recursive audit checks 41 declarations, mostly generated structure projections and recursors, with only standard axiom roots.

`GlobalCuspEnergy318.Data K X g i N` retains the actual modular G function, cusp width, point in the upper half-plane, selected-value equation, local holomorphic differential coefficients and non-Weierstrass condition. Instead of local integrability and local energy bounds, it supplies actual global differential-energy measures on a measurable space X, their mass at most one, and the exact pushforward chart-density identity. X may be the disjoint union of the complex fibers indexed by the embeddings.

`Data.local_energy` derives local integrability and the ordinary disc-area integral bound from those measures, using `GlobalEnergyMeasure318.normalized_chart_energy`. Holomorphy supplies strong measurability; no integrability premise is hidden in the constructor.

`Data.toCusp` constructs the exact frozen `CuspArakelovData318.Data` with unchanged functions, widths, points and non-Weierstrass condition. `Data.actual_archimedean_bounds` then obtains the actual all-embedding averaged logarithmic differential and factorial-Wronskian bounds.

`GlobalEnergyJacobian318.jacobian_quadratic` and `jacobian_49_over_8` compose this constructed data with the existing finite-divisor and Arakelov identities. No local energy bound, coefficient bound, Wronskian bound or final Jacobian bound is supplied. The finite matrix/local coefficient and named minimal-model/Faltings/normalization inputs remain explicit and unchanged.

## Exact remaining geometry

This is a real measure-to-analytic-data constructor, not a construction of a complex algebraic curve or its differentials. The global energy measures, their norm-one normalization and the exact chart-density identities must still be realized by the actual curve and orthonormal differentials. The modular G identification and whole-fiber non-Weierstrass selection remain the same explicit source inputs. The final `GeometricRealization` existence is not proved or asserted here.

## Reproduction

Run `bash converse-work/global-cusp-energy/verify.sh`. It compiles both modules and the exhaustive axiom audit with `debug.skipKernelTC=false`. Frozen upstream packets are not edited. The receipt binds exact source and dependency hashes. No repository or Git changes were made.
