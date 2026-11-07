# Independent review: actual finite étale orbit quotient

Result: accepted at the stated algebraic and affine-scheme scope. The four exact source modules and exhaustive audit were copied to this directory and freshly compiled with kernel checking enabled. All 72 project declarations passed the recursive axiom audit with only propext, Classical.choice, and Quot.sound. Source hashes were checked against the frozen originals after replay.

## Mathematical checks

The fixed algebra is the actual subalgebra of elements fixed by every supplied algebra automorphism. The proof encodes all fixed equations by the linear map b ↦ (g ↦ ρ(g)b-b). Its kernel is established directly. Flat tensor exactness preserves this kernel, and finiteness of the indexing family is used for tensor/finite-product commutation. This proves the canonical invariant-base-change map is an equivalence without averaging and without assuming that the group order is invertible.

An actual equivariant faithfully flat splitting into functions on a finite G-set identifies the fixed algebra with functions on the actual orbit set. The coordinate-function identification is proved, not assumed. Finiteness and étaleness descend, and the original algebra is proved finite étale over the fixed algebra. The automorphisms are deliberately indexed as a family: the equivariance equation correctly accounts for pullback reversing action composition. No unjustified action homomorphism is used.

The affine quotient is literally Spec of that fixed algebra. Both structure and quotient maps are actual Spec maps, are proved finite étale, and satisfy the stated invariance and unique affine factorization property. The algebraic universal property is not silently promoted to an arbitrary sheaf quotient.

## Remaining source realization

The actual primitive-torsion cover, its equivariant faithfully flat splitting, and its identification with the required modular/fppf-sheaf quotient and normalization remain explicit. The reviewed packet does not claim these objects exist merely from the algebraic argument. Nor does it assert the final global geometric realization or FiveContact49Height.

## Reproduction

Run `bash copy/build.sh`. The copy is first on LEAN_PATH, so the replay compiles and consumes the copied project sources. Imported Mathlib oleans are reused. This is an independent project replay and bounded mathematical review, not a recompilation of all Mathlib or an independent proof of the remaining global geometric inputs.
