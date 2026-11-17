# Actual p-adic unit residues and squareclass normalization

Two independent native-only modules are added. PadicUnitSquareclass318 uses Hensel to produce a nonzero square multiplier when unit values agree modulo p at odd primes or modulo8 at2. It extracts an actual integer unit approximation at every positive depth and transports integer CRT congruences back to the local unit. PadicSquareNormalization318 explicitly normalizes any nonzero p-adic value, including negative valuations, to p^alpha times a unit up to a nonzero square, with alpha0 or1. Dividing all coordinates by the same square factor preserves both binary representations.

All1340 predecessor sources and their relative order remain byte-identical. Both new modules import native Mathlib only; the focused union is two roots. No unchecked experiment dependency is introduced.

These are concrete local bridges, not the actual finite-family assembly, auxiliary-prime compatibility, global anchor or four elliptic realizations. Source/API review is not Lean acceptance. No options, resource limits or existing consumers change.
