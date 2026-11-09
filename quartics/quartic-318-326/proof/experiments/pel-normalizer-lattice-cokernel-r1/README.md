# Exact original normalizer lattice cokernels

Construct the exact right-normalizer lattice cokernels of the original integral quaternion order: O/(O*n_p) is explicitly additively isomorphic to(Z/p)^2 for p=2,3,5,7, and the original conjugate lattice map composes in both orders to multiplication byp.

These nonunit maps are injective with nontrivial finite cokernel. They are not asserted to preserve the fixed principal polarization as isomorphisms. The analytic transport must retain its norm multiplier.

## Application obligations

1. **Same original lattice and generators.** Required: Do not substitute a free lattice with the same rank or discriminant. Constructed: All50 predecessors are byte-identical. The right map is multiplication on actual original order elements by the actual specified n_p; coordinate formulas use the existing coordinatesEquiv and product. Evidence: verification/SOURCE-COPIES.json; PELPrimeLatticeResidues318.rightMultiply.

2. **Full prime coverage and conjugation.** Required: Every original prime and the same actual inverse data must be retained. Constructed: Fin4 covers2,3,5,7. Four explicit integer conjugate vectors equal actual star(n_p). Full coordinate products by n_p thenbar(n_p), and in reverse, equalp times every original vector. Evidence: PELPrimeRightLattice318.original_conjugate; right_norm; left_norm.

3. **Actual residue map.** Required: Do not infer a cokernel from determinant or Smith rank alone. Constructed: Two specified coordinates of actual x*bar(n_p), reduced modp, define an additive map from the original integer lattice. The selected rows are stated for every prime. Evidence: PELPrimeRightLattice318.rows; residue; residueHom.

4. **Entire kernel reconstruction.** Required: Vanishing selected coordinates must imply membership in the entire lattice image. Constructed: all_divisible proves all four original product coordinates are divisible byp. kernel_preimage then reconstructs an integer vectorb withb*n_p=a using all four equations. image_zero gives the converse, yielding exact kernel_iff for every vector. Evidence: PELPrimeRightLattice318.all_divisible; kernel_preimage; image_zero; kernel_iff.

5. **Actual surjectivity.** Required: Cokernel cardinality requires complete residue coverage. Constructed: Explicit integer lift matrices give a preimage for every pair in(Z/p)^2. residue_lift is proved on arbitrary residue pairs, then transported through the original coordinatesEquiv. Evidence: PELPrimeLatticeResidues318.liftCoefficients; lift; residue_lift; orderResidue_surjective.

6. **Exact quotient object.** Required: The first-isomorphism theorem must consume the same actual image and kernel. Constructed: kernel_eq_range is an equality of additive subgroups of the original order. Quotient equivalence transports that exact equality and the actual surjective orderResidue map. The quotient is literallyO divided by range(rightMultiply). Evidence: PELPrimeLatticeResidues318.kernel_eq_range; PELPrimeLatticeCokernel318.Cokernel; quotientEquiv; cokernel_card.

7. **Dual compositions and injectivity.** Required: Do not silently identify nonunit multiplication with an integral automorphism. Constructed: The actual conjugateMultiply is integral. Its two compositions with rightMultiply equalp-smul on every original order element, and rightMultiply is injective. The cokernel cardinal is p², namely4,9,25,49, not1. Evidence: PELPrimeLatticeCokernel318.conjugate_after_right; right_after_conjugate; rightMultiply_injective; literal_indices.

8. **Period and canonical boundary.** Required: Lattice index alone does not assert an algebraic isogeny or polarized-family isomorphism. Constructed: This is the exact finite lattice quotient needed by analytic nonunit scalar transport. The actual complex-quotient map/kernel join, holomorphy, polarization multiplier and algebraization are separate. No fixed principal-polarization isomorphism, full canonical deck identification or contact-Jacobian equivalence is claimed. Evidence: README.md; verification/historical-source-pins.json.

9. **Validation.** Required: Independent finite computation is not kernel acceptance. Constructed: Exact checker binds literal conjugate/row/lift tables, verifies full integer polynomial composition and reconstruction identities, all residue vectors at eachp and every output lift, original quaternion multiplication and indexp². Pinned actual quotient and ZMod APIs are inherited. Static53/3 and audit controls pass; no local Lean. Evidence: verification/check_lattice_cokernel.py; verification/PARITY-PRIMARY-SOURCES.json.

## Validation

No local Lean compilation. Hosted strict-module recursive audit and independent acceptance pending. Period-quotient kernel, holomorphic isogeny and polarization multiplier are not consequences silently folded into this lattice statement.
