# Original relative cotangent quotient reconstruction

Draft reconstructed from remote commit 31a0e67e on 2026-11-11. Three new modules and 91 byte-identical dependencies from pel-original-domain-character-union-r112.

The actual transitivity quotient now has a proposed linear equivalence from the quotient by its exact derivative coefficient ideal to the actual relative Kähler module. Its value on every original differential is specified. The finite and infinity specializations retain the original signed root coordinates and send the quotient unit to dz_i and du, respectively. The infinity scalar structure is the actual projective reciprocal parameter v=u².

The final module uses the previously constructed whole finite/infinity derivative-zero ideals, restricted to the original canonical principal opens. It identifies these actual quotient modules with the actual relative cotangent modules, rather than merely matching their annihilator ideals. Both normalization statements retain factor two. This is an affine module comparison. It does not yet construct the global intrinsic relative-cotangent sheaf isomorphism on the closed zero scheme, reducedness, stalk lengths, or their sum 40.

The remembered later packet 847 could not be recovered from the available checkout or backup. This is new reconstruction from exact available sources, not recovery or acceptance of that packet. Historical justification outside the inspected source packets remains unresolved.

No local Lean build, replay or profiling was run. Static dependency/source checks are not kernel acceptance. Hosted Lean verification and independent source review remain pending. No PEL identification, numerical rational branch parameters, or unconditional arithmetic theorem is claimed.

## Exact input and maps

- PolynomialRelativeCotangentFrame318 supplies surjectivity and the full kernel of the original transitivity map. Those proofs are retained byte-for-byte.
- The first isomorphism theorem is applied to that same map, in its forward direction, after the exact ideal equality. No abstract cyclic module replaces the relative Kähler module.
- Finite charts use all i in Fin 4 and arbitrary b. Infinity uses the original injective b and its actual canonical neighborhood, covering all eight infinity centers as established in the predecessor.
- FourRootDerivativeFiniteIdeal318.derivative_ideal and FourRootDerivativeInfinityIdeal318.derivative_ideal identify the actual whole zero ideals after their actual localization maps. Their equalities are the input to the final module.
- Pinned upstream: mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679, LinearAlgebra/Isomorphisms.lean (quotKerEquivOfSurjective and its apply_mk theorem), LinearAlgebra/Quotient/Defs.lean (quotEquivOfEq and its apply_mk theorem). These primary definitions were read directly before writing the new applications.
