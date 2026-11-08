# Constructed monic splitting and literal primitive-two family

## Actual construction

`MonicRootEtale318` derives the unit derivative in an actual monic separable polynomial quotient from its Bezout identity. The derivative localization in the standard-etale presentation is therefore trivial. A positive-degree quotient is finite free and faithfully flat.

`MonicEtaleSplitting318` constructs a splitting extension by adjoining a root, dividing by its monic linear factor, and repeating by degree induction. Every step is finite etale and faithfully flat. The final ring and complete factorization are constructed; neither a splitting ring nor a factorization is an input.

`SplitPolynomialAlgebra318` derives pairwise coprimality of the linear factors from separability. The actual evaluation algebra map is proved injective by coprime divisibility and surjective by the Chinese remainder theorem.

`MonogenicSplitEquiv318` constructs the arbitrary-base-change isomorphism for the polynomial quotient and binds the product decomposition to evaluation on every pure tensor. Thus the actual splitting has the exact formula s tensor f(root) maps to the function i maps to s times f(r_i).

## Source application at two

`ShortTwoTorsion318` uses the literal cubic x^3+A*x+B. An explicit discriminant Bezout identity proves separability when -16*(4*A^3+27*B^2) is a unit. Its actual quotient is finite free of rank three, etale and faithfully flat.

`TwoTorsionCurve318` constructs its closed immersion into the actual short-Weierstrass affine scheme by x maps to the quotient root and y maps to zero. It proves the exact universal y=0 factorization over every coefficient algebra, including rings with nilpotents. Its structure morphism is finite, etale, flat and surjective.

`TwoTorsionPoints318` proves the cubic's roots give actual elliptic points of exact order two under Mathlib's field-point group law, and every affine point of exact order two has y=0. No group-law or order predicate is supplied as a hypothesis about the polynomial roots.

`LiteralTwoTorsion318` specializes the construction to the actual `OpenJModel318.integralModel` coefficients. The base localization level N may be any nonzero natural, but the torsion constructed here is always two-torsion. `PrimitiveTwoModel318` specializes the base level to two, explicitly identifies the three labels with the existing primitive pairs modulo two, constructs the diamond-equivariant splitting, and supplies the preceding pointed proper-model construction with this actual cover and splitting. The modulo-two diamond action is trivial, as proved from the actual unit group. A field-valued cover point is still supplied when selecting a point-preserving component.

## Exact limitations

This constructs the literal cubic family, its y=0 universal property, its geometric field-point interpretation, and its actual finite-etale splitting. It does not claim a formally proved identification with the kernel of a complete relative multiplication-by-two Scheme morphism: the full relative group law has not yet been finished. It also does not construct primitive N-torsion for general N, prove the general diamond-equivariant torsion splitting, or identify this auxiliary modular construction with the specified PEL/Shimura source.

The discriminant-210 PEL canonical model and universal abelian surface, controlled fields and good reduction, regular/semistable resolution, maximal Hodge/KS structures and Arakelov realization remain separate. No unconditional `RefinedGeometricRealization`, `FiveContact49Height` or final Diophantine theorem is asserted.

## Replay

Run `flock -x ../compile-coordination/heavy.lock bash build.sh` from this packet directory when the shared compiler coordinator releases the slot. The build is sequential. All nine modules are rebuilt with `debug.skipKernelTC=false` and every declaration is recursively audited for standard axiom roots only: `propext`, `Classical.choice`, `Quot.sound`. Imported dependencies use the pinned checked cache, not a fresh rebuild of the entire dependency closure. This is author verification, not independent review.

The frozen whitelist is in receipt.json and SHA256SUMS. Diagnostic sources, logs and compiled artifacts outside the whitelist are not deliverables. No manuscript or shared repository files were edited by this worker.
