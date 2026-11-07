# Actual integral lattice action descent

`IntegralLatticeDescent318.finite_image_action_trivial` proves the coordinate-free version of the mod3 Hom-lattice descent step.

Inputs:
- An additive commutative group H with a finite-rank free integral module structure.
- A group representation `rho:G ->* (H ≃ₗ[Z] H)` with finite image.
- For every g and x, an actual y in H satisfying `rho(g)(x)-x=3*y`.

Conclusion: every `rho(g)` fixes every vector of H.

The proof selects an integral basis internally, constructs the actual matrix representation, and proves its reduction is the identity from the displayed vector differences. It then applies the checked finite-order matrix congruence theorem in `hom-congruence-bridge`. No chosen matrix, torsion-free action theorem, or basis-to-matrix compatibility hypothesis is supplied by the caller.

This is directly the algebraic interface produced by the source's abelian Hom argument. Constructing H as the actual geometric Hom lattice, proving its finite/free properties and finite Galois image, the factorization of a map killing A[3] through [3], and geometric descent remain separate arithmetic-geometric inputs. The module does not claim to formalize those constructions.

Strict-kernel replay: `bash run.sh`. The source imports the frozen three-module congruence packet without changes. The exhaustive recursive axiom audit of the new module permits only propext, Classical.choice and Quot.sound. Logs, exact source hashes, and the imported packet receipt hash are included. No repository/Git modifications were made.
