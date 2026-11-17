# Local binary norm producer at good odd primes

One native-only source is added. For every odd prime p not dividing the integer coefficients a and b, it constructs an actual p-adic affine witness z²-a*x²=b. The finite-field intersection theorem gives a residue solution. Hensel varies the homogenizing coordinate around1, with derivative-2b a unit; the lifted coordinate is nonzero, permitting division. No local-solubility premise is assumed.

All1338 predecessor sources and their relative order remain byte-identical. The new source imports native finite-field, Hensel and tactic modules only, so its experiment-root closure is one. No uncompiled experiment dependency is added.

The scope is exactly ordinary odd primes outside2ab. Bad primes, the auxiliary selected prime, CRT/Dirichlet selection and global ternary descent remain separate obligations. No actual global anchor or four elliptic realizations are produced. Source/API review is not Lean acceptance; strict hosted checking remains required.
