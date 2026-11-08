# Literal relative three-torsion family

This packet constructs the actual finite-etale rank-eight nonzero-three-torsion equation family over a smooth short-Weierstrass coefficient ring with three invertible. Its field-point interpretation uses the actual elliptic group law; it is not an assumed torsion predicate.

## Constructed objects

- `ThreeTorsionIdentity318` proves the literal third-division polynomial identity, its derivative, and an explicit Bezout identity against the elliptic cubic over every commutative coefficient ring.
- `ShortThreeTorsion318` normalizes the quartic using the inverse of three. The actual quotient algebra is finite free of rank four, etale and faithfully flat. Its splitting extension is constructed by the earlier monic polynomial splitting algorithm. The elliptic cubic becomes an actual unit in this quotient.
- `ThreeTorsionAlgebra318` adjoins a square root of that actual cubic value. The resulting algebra is finite free of rank eight, etale and faithfully flat over the original ring. Its actual x,y elements satisfy the short-Weierstrass equation and y is a unit.
- `ThreeTorsionPoints318` proves that a nonsingular field-valued point has exact additive order three if and only if its x-coordinate is a root of the literal third-division polynomial. The proof derives P+P=-P from Mathlib's actual elliptic doubling formula and proves the converse. No supplied group-law or order premise about polynomial roots is used.
- `ThreeTorsionFunctor318` proves the normalized and literal division equations equivalent after any coefficient-algebra extension. It constructs an equivalence between algebra maps from the actual rank-eight ring and solutions of the two equations, over arbitrary commutative coefficient algebras, including algebras with nilpotents.
- `ThreeTorsionScheme318` constructs the actual scheme, its morphism to the affine elliptic family, and its finite, etale, flat, surjective structure map. The morphism to the elliptic scheme is proved to commute with the base maps.
- `LiteralThreeTorsion318` specializes the construction to the actual `OpenJModel318.integralModel` coefficients with no extra discriminant or invertibility assumptions. The localization level N can be any nonzero natural, but the constructed torsion order is always three.
- `ThreeTorsionFieldPoints318` binds the actual representing equations over every coefficient field extension to exact order-three points on the actual base-changed elliptic curve.

## Exact boundaries

This is a literal relative equation construction with a universal property and exact field-point interpretation. It does not yet identify the family as the kernel minus identity of a completed relative multiplication-by-three Scheme morphism. The complete relative group-law axioms are separate work. No closed-immersion theorem for the new inclusion is claimed here.

The rank-four x-coordinate splitting is constructed; a full diamond-equivariant splitting of the rank-eight family by the eight primitive pairs modulo three is not yet supplied. Primitive torsion and such a splitting for general N remain open. None of these auxiliary open-j constructions is silently identified with the discriminant-210 PEL curve, its universal abelian surface, a full principal-three marking, or the source's controlled degree-576 field.

The actual PEL canonical model/comparison, regular or semistable models, controlled fields and good reduction, Hodge/KS and Arakelov realization, and the unconditional Diophantine endpoint remain separate. No new manuscript incorporation or independent whole-proof acceptance is asserted.

## Verification and provenance

Run `flock -x ../compile-coordination/heavy.lock bash build.sh` from this packet directory. All eight modules are sequentially rebuilt with `debug.skipKernelTC=false`; `Audit.lean` recursively checks every declaration and permits only `propext`, `Classical.choice`, and `Quot.sound` as axiom roots. Imported dependencies use the checked cache, not a fresh rebuild of the entire dependency closure. The frozen receipt records the exact verified source and log whitelist. This is author verification, not independent review.

`ThreeTorsionIdentity318.lean` was recovered from an unfinished preceding attempt; its cubic-unit proof was repaired before replay. Other source modules in this packet are the present continuation. No manuscript, shared branch, or PR was edited by this worker.
