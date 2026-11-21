# Exact RC62 r3 proof-only repair

Parent r2 run 44846436037, artifact 14683244176: 33 compile-pass, 445 audited, six compiler-error roots, 23 import-blocked, 42 not selected. Main target stays `CTActualGloballyFiniteIsogenySelmer318` under the same exact 62 project modules (0 baseline). The complete 104-module package is retained; 98 Lean bytes unchanged per file. This successor is source only, not checked with Lean.

- Krull coordinate orbit and field primitive boundary explicitly publicly import AbsoluteGaloisGroup where needed in public types, retaining the exact original Galois action/topology and primitive class API.
- Closed finite Galois layer gives the exact normal restriction an explicitly typed base/source/codomain, as in pinned Mathlib Galois.Profinite restriction-continuity theorem. This only resolves hidden base field inference; actual same closed subgroup and normal layer remain.
- Composite coordinates and literal dual fiber explicitly import the pinned public characteristic-zero interface. Composite also renames the reserved lambda token to `slope`; the actual slope and both coordinate expressions are unchanged.
- Prime monomials derives positivity from the already-imported nonzero product lemma and positive natural characterization, and annihilates the explicit Nat-to-Int-to-ZMod 2 valuation multiplier by `Int.cast_natCast` and `ZMod.natCast_self`. Same arithmetic squareclass separation.

The endpoint assembles literal local conditions at all places and the same retained finite subgroup. It is not prime Selmer corank, Mordell–Weil rank, analytic rank, or a Cassels–Tate pairing. The 104-module finite-scalar ratio terminal was not selected in the parent run and is not automatically verified by a future pass of 62.
