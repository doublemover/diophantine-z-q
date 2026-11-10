# Actual integer dual incidences for the original conic lattice family

All286 predecessor sources remain byte-identical. This is a concrete route toward the missing lattice-tail estimate, not an assumed successive-minima theorem.

LiteralDualLineIncidence318 uses the literal conic generators(1,κs²,s) and(0,1,0). A nonzero dual vector annihilates at mostTWO directions, including infinity. The proof constructs the quadratic root bound by factoring around one actual root; when the z coefficient vanishes it handles the linear/infinity case directly. Zero dual reduction is explicitly the FULLp+1 exception. No primitive-vector assumption deletes it. Nonzeroκ remains explicit.

LiteralIntegerDuality318 connects these local direction incidences to the ACTUAL integer sublattices. If the direction pairing vanishes, every integer point in the literal kernel has dot product divisible by the prime. Conversely the existing CRT constructs one actual integer vector simultaneously reducing to every selected generator, and that vector belongs to the original lattice. The resulting original_duality_iff says that M divides dot(v,u) for EVERY original lattice vectoru exactly when all original local direction pairings vanish. It does not replace the integer lattice by its image or invoke an unproved lifting/saturation assertion.

OriginalDualIncidenceCount318 then constructs the exact equivalence between original integer-lattice incidence parameters and the product of actual local direction types. It proves #incidences(v)<=2^omega(M)*zeroModulus(v), where zeroModulus is the product of EXACTLY those retained primes dividing ALL THREE ORIGINAL integer coordinates ofv. Nonzero local reductions contribute at most2; zero reductions contribute at most2p. The zero-reduction criterion is explicitly proved as simultaneous integer divisibility, not rational-coordinate rescaling.

## Quantitative boundary
This is a fixed-vector incidence estimate. It is not yet summed over short vectors, and the geometric transference step from a large third successive minimum to a short nonzero dual vector is still missing. No lattice-tail or weighted obstruction bound is inferred merely from the index, local incidence count or existence of the original basis. The real-lattice embedding and normalizationv/M must be built before any Euclidean dual/minimum statement. Originalκ and the literal source correction remain intact.

Validation:5467 actual local dual-vector counts;81000 actual global integer-lattice annihilation equivalences;3375 original-vector global incidence bounds; negative controls forzeroκ andzero dualvector. Static289/222 source-policy/dependency closure pass. No local Lean compile.
