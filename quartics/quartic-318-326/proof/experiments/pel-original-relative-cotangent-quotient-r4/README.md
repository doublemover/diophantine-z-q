# Original relative cotangent quotient reconstruction

Narrow successor to frozen pel-original-relative-cotangent-quotient-r1 on 2026-11-11. One proof-only simplification repair; all other 93 Lean sources are byte-identical r1 copies. The three reconstructed mathematical modules are unchanged.

The actual transitivity quotient now has a proposed linear equivalence from the quotient by its exact derivative coefficient ideal to the actual relative Kähler module. Its value on every original differential is specified. The finite and infinity specializations retain the original signed root coordinates and send the quotient unit to dz_i and du, respectively. The infinity scalar structure is the actual projective reciprocal parameter v=u².

The final module uses the previously constructed whole finite/infinity derivative-zero ideals, restricted to the original canonical principal opens. It identifies these actual quotient modules with the actual relative cotangent modules, rather than merely matching their annihilator ideals. Both normalization statements retain factor two. This is an affine module comparison. It does not yet construct the global intrinsic relative-cotangent sheaf isomorphism on the closed zero scheme, reducedness, stalk lengths, or their sum 40.

The remembered later packet 847 could not be recovered from the available checkout or backup. This is new reconstruction from exact available sources, not recovery or acceptance of that packet. Historical justification outside the inspected source packets remains unresolved.

No local Lean build, replay or profiling was run. Static dependency/source checks are not kernel acceptance. Hosted Lean verification and independent source review remain pending. No PEL identification, numerical rational branch parameters, or unconditional arithmetic theorem is claimed.

## Exact input and maps

- PolynomialRelativeCotangentFrame318 supplies surjectivity and the full kernel of the original transitivity map. Its proof now explicitly simplifies RingHom.id_apply after Algebra.algebraMap_self; statements and maps are unchanged.
- The first isomorphism theorem is applied to that same map, in its forward direction, after the exact ideal equality. No abstract cyclic module replaces the relative Kähler module.
- Finite charts use all i in Fin 4 and arbitrary b. Infinity uses the original injective b and its actual canonical neighborhood, covering all eight infinity centers as established in the predecessor.
- FourRootDerivativeFiniteIdeal318.derivative_ideal and FourRootDerivativeInfinityIdeal318.derivative_ideal identify the actual whole zero ideals after their actual localization maps. Their equalities are the input to the final module.
- Pinned upstream: mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679, LinearAlgebra/Isomorphisms.lean (quotKerEquivOfSurjective and its apply_mk theorem), LinearAlgebra/Quotient/Defs.lean (quotEquivOfEq and its apply_mk theorem). These primary definitions were read directly before writing the new applications.

## Hosted failure and narrow repair

Hosted batch214 failed in PolynomialRelativeCotangentFrame318 at line53: after Algebra.algebraMap_self, the goal still contained `(RingHom.id S) ((algebraMap R[X] S) X)`, whereas Derivation.map_algebraMap gave the unwrapped argument. The successor adds only RingHom.id_apply to that simp-only list. It changes no hypothesis, statement, coefficient, transitivity map, ideal or consumer. The exact hosted diagnostic is in build/ci214-cotangent/logs/PolynomialRelativeCotangentFrame318.log.

Other active copied consumers found at repair time are pel-original-domain-character-union-r113, pel-original-zero-local-length-r1 and pel-original-zero-scheme-reduced-r1. All remain frozen; this packet neither repairs nor asserts hosted acceptance of those copies. Independent review and hosted rerun of this successor are pending. Separate later packets address reducedness and local quotient lengths; the genuine global cotangent sheaf comparison remains open.
