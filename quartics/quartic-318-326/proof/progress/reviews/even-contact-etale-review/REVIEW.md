# Independent normalized even-contact cover review

Accepted at the stated scope. A copied strict-kernel replay of EvenContactEtale318 and EvenContactCover318 passes all 32 recursively audited declarations. Their source hashes were compared to the frozen originals before and after replay. Only propext, Classical.choice and Quot.sound occur. This is a fresh rebuild of the two modules, not their entire imported Mathlib dependency closure.

## Mathematical and application check

The actual root algebra is AdjoinRoot(X^2-u) for a unit u, over an arbitrary commutative ring. Its tautological root squares to u and is itself a unit. With 2 a unit the derivative 2T is a unit in this actual root algebra. Therefore the standard-etale derivative localization is genuinely trivial; the algebra equivalence to the standard-etale presentation is not an assumed etaleness certificate.

The monic quadratic gives actual finiteness and freeness. When the base is nontrivial, the algebra has actual rank two and is nontrivial. Thus its proved faithful flatness and the resulting surjective Spec map do not inadvertently allow an empty covering algebra. The finite and etale scheme morphisms are exactly the spectrum map induced by the original base-ring algebra map.

For even contact u*pi^(2k), the normalized root T*pi^k is in this etale algebra and has the required square. The factorization lemma covers every field-valued generic root y when the image of pi is nonzero: y/pi^k is a root of X^2-u, yielding the actual algebra map and hence the actual Spec point above the base. It does not assume an already chosen unramified field or a square root in the base ring. The hypothesis excluding pi=0 is visible; this is a generic-branch factorization, not a claim covering every point of the singular unnormalized special fiber.

The point-map composition uses the actual algebra-hom base compatibility, with the correct contravariant direction. No incorrect characteristic restriction or unproved global-model identification was found.

## Retained scope

Identification of this normalized algebra with a particular local model or branch of the global Shimura/modular fiber is external. The packet does not itself construct the global integral curve or abelian scheme. Its source use as the local even-contact etale root producer is sound.
