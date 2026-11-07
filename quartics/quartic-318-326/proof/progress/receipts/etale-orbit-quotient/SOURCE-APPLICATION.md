# Point-level modular open: the quotient portion

The actual source open is U = Spec Z[1/(6N), j, 1/(j(j-1728))]. The separate OpenJModel318 module has already constructed the literal Weierstrass curve over this ring and proved its discriminant invertible. The classical integral-cover producer constructs its primitive N-torsion scheme T and the scalar diamond action H on it.

On a faithfully flat cover on which T is a constant finite set X, its coordinate ring is the function ring X -> S. A scalar diamond action on points gives pullback f -> (x -> f(g*x)). Its actual invariant algebra consists precisely of functions constant on the H orbits. The orbit set, rather than a Reynolds operator, produces the quotient algebra. This works even when the residue characteristic divides |H|.

The key descent assertion is now proved in Lean. Write rho for the actual family of algebra automorphisms of B. The fixed algebra is the kernel of the linear map b -> (g -> rho(g)(b)-b). For flat S/R, tensoring this exact sequence remains exact. Because G is finite, tensor commutes with its function module. Thus the canonical map S tensor B^G -> (S tensor B)^G is an algebra isomorphism. No faithful-flat descent datum is assumed for this particular equality. Faithfulness is used only afterward to descend finiteness and etaleness from the explicit orbit-function algebra.

The actual spectrum Spec(B^G) and both maps Spec(B) -> Spec(B^G) -> Spec(R) are consequently constructed and proved finite etale. For an invariant R-algebra map C -> B, the actual unique factor C -> B^G is provided. Thus every affine-target quotient factorization is checked.

The new proof is compatible with arbitrary later base extension: the constructed quotient algebra remains finite etale. This statement does not assert that an arbitrary base extension commutes with invariants without proof; the base-change equivalence proved in this packet assumes flatness. In the integral-model application one can instead base-change the already constructed quotient and identify it with the normalization using the separate actual normality and generic-fiber argument.

What is still not constructed in Lean here is T itself, the actual splitting S and its point labels, the full moduli/sheaf quotient identification, or the normalization/gluing model. These are real geometric realization inputs, not replaced by another numerical bound. The frozen INTEGRAL-COVER-PRODUCER gives their classical source-level proof; this packet closes exactly its invariant-algebra and finite-etale quotient arithmetic-geometric step.
