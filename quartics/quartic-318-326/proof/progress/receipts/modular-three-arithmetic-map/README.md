# Actual modular quotient to the specified arithmetic model

This packet constructs a genuine map from the already-defined analytic Gamma1(3) orbit quotient, away from j = 0 and 1728, to complex points of the specified integral arithmetic full diamond fixed algebra.

- Prove that the canonical, sign-independent x-scale transforms with actual modular weight two.
- Use the genuine standard elliptic point represented by the period 1/3. Its actual x-coordinate divided by that canonical scale is invariant under the actual Gamma1(3) group.
- Construct a ring homomorphism from the literal arithmetic normalized third-division quartic to the complex numbers, using the already-proved exact root equivalence. Prove its coordinate formula and its base restriction to evaluation at genuine analytic j.
- Transfer the ring homomorphism to the full fixed algebra, using the actual fixed-algebra isomorphism rather than an assumed four-point labeling.
- Descend it to the existing analytic Gamma1(3) quotient by proving representative independence from actual marked-period transport. Package every image as an actual Spec(C)-valued point of the specified arithmetic affine scheme, and prove exact j compatibility.
- Prove that every Gamma0(3) matrix is in Gamma1(3) up to the central sign. Therefore the extra effective sign does not double count source points, and the arithmetic point is Gamma0(3)-invariant as well. This is specific to level three and is not asserted for general levels.

This is an actual source-to-arithmetic-model map, not a global isomorphism. Global injectivity/surjectivity, holomorphic variation of the standard torsion coordinate, extension through the excluded elliptic values/cusps, and a PEL identification remain unproved here. The positive integer N parameterizes the localization of the arithmetic base; the torsion order in this packet is three.

Verification: sequential Lean 4.35.0 replay with debug.skipKernelTC=false, followed by an exhaustive recursive import-all axiom audit of public, private, and generated declarations. Only propext, Classical.choice and Quot.sound are allowed. This is an author replay against pinned predecessor/Mathlib caches, not an independent review or full dependency-closure replay. Run build-all.sh only while holding the exclusive workspace compile lock.
