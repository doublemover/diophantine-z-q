# Actual maximal-order level-three reduction

Construct the literal reduction O/3O of the same explicit maximal quaternion order and derive its radical, residue field and effective level-three kernel counts.

This is a direct coordinate construction, not a replacement of the original order by an unrelated finite algebra. It discharges the local-ring and counting inputs of the earlier LevelThreeKernel route while keeping its actual geometric group-extension premise explicit.

## Application obligations

1. **Historical route and current scope.** Required: Do not describe the old local classification argument as absent merely because it was not Lean. Constructed: Read the actual quaternion-local-reduction receipt: its completed maximal-order classification, coordinate reduction and unit interpretation were prior justification. This packet supplies a direct formal coordinate route for the now-constructed original O, without assuming local classification. Evidence: verification/historical-source-pins.json.

2. **Same maximal order.** Required: Reduction must consume the exact order and period lattice. Constructed: All16 predecessors are byte-identical; B=(-210,5), basis[1,i,(1+j)/2,i/2+k/10], Rosati and perfect form remain unchanged. Evidence: verification/SOURCE-COPIES.json.

3. **Full multiplication and surjectivity.** Required: A four-coordinate additive model alone is not a ring model. Constructed: The actual order maps to QuaternionAlgebra(F3)0 0 2 by(a0−a2,a1−a3,−a2,a3). Entire original multiplication table commutes; inverse coordinate lift uses integer surjectivity toF3. Evidence: PELOrderReductionThree318.reduction; reduce_product; reduction_surjective.

4. **Exact quotient kernel.** Required: The quotient must be literal modulo3O, including every negative coordinate. Constructed: All four reduction coordinates vanish iff all integer basis coefficients are divisible by3. The resulting original order element is exactly3 times another original order element; difference gives the full ring-congruence relation. Evidence: PELOrderReductionThree318.kernel_iff_three; moduloThree_iff.

5. **Noncommutative quotient and residue.** Required: Do not impose a commutative ring instance on quaternion order or its reduction. Constructed: RingCon quotient and its surjective first-isomorphism theorem preserve the actual noncommutative structure. Residue is genuine QuadraticAlgebra(F3)2 0; exhaustive three-base-element no-root proof supplies its Field instance. Evidence: PELOrderReductionThree318.quotientEquiv; PELReductionResidueField318.quadratic_no_root; residue.

6. **Entire radical.** Required: Unit lifting requires square-zero kernel, not a guessed finite cardinality. Constructed: The actual residue map kills exactly real and j coordinates. Every product of two kernel elements is zero; residue map surjective, field has9elements, ring has81 through exact coordinate equivalences. Evidence: PELReductionResidueField318.radical_coordinates; radical_mul_zero; residue_card; reduction_card.

7. **Actual level consumer.** Required: The downstream36 must refer to literal O/3O and its actual scalar signs. Constructed: The exact quotient residue map feeds existing LevelThreeKernel318 on the same quotient ring, deriving radical9, full units72 and central sign quotient36 without ring/cardinality premises. Evidence: PELActualLevelThreeQuotient318.actual_counts.

8. **Remaining geometric inputs.** Required: A finite quotient count is not itself the PEL abelian scheme, Tate module or full deck group. Constructed: The displayed576 conclusion still requires an actual group extension with this kernel and W. No global order-unit or norm-one-unit surjectivity is asserted; Tate freeness/marking, algebraic family/moduli realization and contact-to-PEL identification remain separate. Evidence: PELActualLevelThreeQuotient318.actual_extension_card; README.md.

9. **Validation and primary APIs.** Required: Source checks and finite computations are not Lean kernel acceptance. Constructed: Pinned RingCon.Hom, ZMod.Basic, QuadraticAlgebra.Basic and actual LevelThreeKernel producer were read. Independent exact6561-product/radical/unit/sign checker and source closure pass; hosted recursive audit and independent acceptance pending. Evidence: verification/check_reduction.py; verification/primary-library-source-pins.json; verification/baseline-source-pins.json.

## Validation

No local Lean compilation or build. Static closure and exhaustive finite computations are not a kernel PASS. Independent source review and hosted recursive audit pending. No complete PEL moduli or full arithmetic theorem claim.
