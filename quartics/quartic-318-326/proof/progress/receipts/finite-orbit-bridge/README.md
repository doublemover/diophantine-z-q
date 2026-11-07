# Finite vector orbits produce finite lattice image

`IntegralLatticeDescent318.finite_image_of_basis_orbits` proves that an actual linear representation has finite image whenever its finitely many integral basis vectors have finite orbits. The proof embeds the actual image into the finite product of the basis-vector orbit sets; injectivity follows from determination of a linear map on a basis.

`IntegralLatticeDescent318.finite_orbit_action_trivial` is the basis-free combined theorem. For a finite-rank free Z-module H, it requires only:
- An actual action by integral linear automorphisms.
- Every individual vector orbit is finite.
- Every difference sigma(x)-x is three times a vector in H.

It derives finite image internally, then applies the checked lattice and mod3 matrix-kernel proofs to conclude that every vector is fixed. Neither a prechosen matrix action nor a finite-image assumption is required in this final interface.

For the actual abelian Hom application, finite definition fields supply the finite individual orbits. The geometric construction of those fields, finite freeness of the Hom lattice, factorization through [3], and Galois descent remain explicit external arithmetic-geometric facts.

The original Hom-congruence and integral-lattice packets are unchanged. Run `bash run.sh` for the fresh strict-kernel replay and exhaustive standard-axiom audit. Two new declarations are checked in one module. Hashes bind the new source and imported packet receipts. No repository/Git edits were made.
