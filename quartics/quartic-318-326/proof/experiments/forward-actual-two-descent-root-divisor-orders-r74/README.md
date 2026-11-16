# Actual p-adic solutions to primitive integer residues

One source module is added. LegendrePadicPrimitiveResidues318 scales an actual nonzero homogeneous p-adic solution by a largest-norm coordinate. All coordinates become integral and one becomes exactly one. Native depth2 approximants then produce integer residues satisfying the same equation modulo p squared, with at least one coordinate not divisible by p. No integrality or unit-coordinate premise is added.

All 1331 predecessor sources and their relative order are retained exactly. This new module has a single experiment-root closure importing only native RingHoms and Mathlib.Tactic; it does not depend on the draft modular-root module. No affine-transfer module is included.

Source/API review is not Lean acceptance. No local Lean was run. Squarefree coefficient normalization, CRT assembly, complete ternary descent, auxiliary-prime compatibility and simultaneous elliptic realizations remain separate obligations. All actual conditional arithmetic inputs remain unchanged.
