# Exact trace-dual saturation and integral overorders

Prove that norm-integrality cuts the exact quaternion order trace dual back down to the original perfect lattice, excluding any larger subring with integral reduced trace and norm.

This twelve-source span retains the original perfect period lattice and concrete division algebra. It advances the maximality prerequisite without claiming the missing general integrality-to-reduced-invariants theorem or an actual PEL moduli identification.

## Application obligations

1. **Same algebra and integral order.** Required: The overorder result must concern the actual period lattice. Constructed: All nine predecessor sources are unchanged. The same subring uses the basis1,i,(1+j)/2,i/2+k/10, the same positive involution and the same unrescaled trace pairing. Evidence: verification/SOURCE-COPIES.json.

2. **Actual trace-dual inversion.** Required: An unspecified dual lattice or equal-rank substitute is insufficient. Constructed: Four literal tests Tr(x*e_i)=a,b,c,d give x=(a/2,−b/420,−a/10+c/5,−b/420+d/210), by the exact quaternion multiplication and same Gram. Evidence: PELTraceDualSaturation318.trace_coordinates.

3. **Norm and local factors.** Required: All coefficients and exceptional primes must survive normalization. Constructed: The exact norm times210 is F=42a²+42ac−b²+5bd−42c²−5d². All primes2,3,5,7 dividing210 are explicitly used. Evidence: PELTraceDualSaturation318.norm_dual.

4. **Residue coverage.** Required: Finite local obstructions must cover every residue and the coupled conditions. Constructed: Full residue computations force b,d=0 at2,3,7, and b=0,a−2c=0 at5. Their combined conclusion is210|b,42|d,5|(a−2c). No condition at5 is dropped or replaced by independent coordinate vanishing. Evidence: PELTraceDualResidues318.

5. **Constructed lattice membership.** Required: Congruences must recover the original integral basis. Constructed: Writing b=210B,d=42D,a−2c=5A explicitly constructs original coordinates(c+3A,2B−D,−A,−5B+2D), whose embedding equals the same trace-dual quaternion. Evidence: PELTraceDualSaturation318.dual_integral_norm_mem.

6. **Actual overorder maps.** Required: The comparison must use ring closure and the specified inclusion. Constructed: For S containing the original order, trace-integrality on S applies to each actual product x*e_i. Norm-integrality on the same x then proves x belongs to the original order; antisymmetry gives S=O. Evidence: PELIntegralOverorder318.no_larger_integral_overorder.

7. **Nonvacuous integral order hypotheses.** Required: The constructed order must itself satisfy the stated conditions. Constructed: Reduced trace and reduced norm are proved integer-valued on the original order, using its actual integer coordinates. Evidence: PELIntegralOverorder318.order_trace_integral; order_norm_integral.

8. **Remaining maximality/moduli bridge.** Required: A conditional overorder theorem is not yet all module-finite orders or an abelian scheme. Constructed: The bridge from arbitrary module-finite integral orders to reduced trace/norm integrality, exact local ramification classification, PEL scheme algebraization and contact identification remain separate. No generic maximal-order instance or principal polarization of an algebraic scheme is asserted here. Evidence: README.md.

9. **Source review and verification.** Required: Exact application and all prior scope boundaries must be independently reviewed. Constructed: The explicit dual Gram was derived from the prior pinned trace determinant, all187 local residue cases and symbolic reconstruction recomputed. Nine source copies, source-level proofs, static checks and historical controls are bound. Hosted Lean remains pending; no local build. Evidence: verification/check_saturation.py; verification/primary-library-source-pins.json.

## Validation

Static source closure and exact symbolic/residue checks are separate from formal kernel acceptance. No local Lean compilation or build. Hosted recursive audit and independent acceptance pending. No full arithmetic theorem is claimed.
