# Concrete quaternion division and exact order discriminant

Prove division of the specific rational quaternion algebra B=(-210,5) by actual norm anisotropy and compute the exact reduced-trace discriminant of the same perfect integral order.

This is a connected nine-source successor to the exact integral order and perfect trace pairing. All six predecessors are unchanged. The rational algebra is now proved division by a full infinite descent; the determinant computation does not silently supply maximality or local classification.

## Application obligations

1. **Same algebra and lattice.** Required: The PEL prerequisites require the concrete quaternion and lattice already constructed, not a replacement with the same dimension. Constructed: All six preceding sources are byte-identical. The norm is r²+210i²−5j²−1050k² on QuaternionAlgebra Q(-210,0,5), and the lattice basis remains1,i,(1+j)/2,i/2+k/10. Evidence: SOURCE-COPIES.json.

2. **Exact residue obstruction.** Required: A nonzero norm-zero element must be ruled out, not excluded as a premise. Constructed: The literal mod3 equations first force r,j to vanish, then after division by3 force i,k to vanish. Finite residue checks cover all3^4 tuples in both stages. Evidence: PELQuaternionAnisotropy318.outer_residues; inner_residues; coordinates_divisible_three.

3. **Unbounded integer domain.** Required: A bounded coefficient search does not establish anisotropy. Constructed: Strong induction on the sum of all four integer absolute values gives a strictly smaller tuple after dividing every coordinate by3. Zero and negative coordinates are included. Evidence: PELQuaternionAnisotropy318.integer_descent.

4. **Actual rational carrier.** Required: Integer anisotropy alone does not cover the rational quaternion algebra. Constructed: All four rational denominators are multiplied into one explicit nonzero D. The original norm scales by D², and the four resulting integer coordinates force each original rational coordinate to vanish. Evidence: PELQuaternionAnisotropy318.rational_anisotropic; reducedNorm_ne_zero.

5. **Genuine division conclusion.** Required: Nondegeneracy of a bilinear form is not division of an algebra. Constructed: For every actual x≠0, the displayed reciprocal is Nrd(x)^-1 times bar(x). Both multiplication orders are proved1 and yield an actual IsUnit witness. Evidence: PELQuaternionDivision318.mul_reciprocal; reciprocal_mul; every_nonzero_isUnit.

6. **Exact trace discriminant.** Required: A named discriminant must be computed on the specified order, including basis and sign. Constructed: The reduced-trace Gram is explicitly[[2,0,1,0],[0,-420,0,-210],[1,0,3,0],[0,-210,0,-84]], determinant−210². The same order alternating Gram has determinant1. Evidence: PELOrderTraceDiscriminant318.

7. **Period compatibility retained.** Required: The analytic period quotient must retain the exact order and sign. Constructed: No period source or order coordinate changes. Analytic consumes the same six sources and explicitly uses−E for upper-half-plane positivity; the new division proof does not modify that pairing. Evidence: PELPrincipalOrderCoordinates318; README.md.

8. **Remaining classification and geometry.** Required: Division over Q and an order determinant do not themselves establish maximality or all local invariants. Constructed: The exact local ramification set, maximal-order theorem, represented/algebraized PEL abelian scheme and original contact/moduli comparison remain explicit separate joins. No identification of genus5 contact Jacobian with dimension2 surface is made. Evidence: README.md.

9. **Validation and provenance.** Required: The changed application needs source-level review and hosted kernel checking. Constructed: Read the actual accepted integer/rational descent pattern in AnchorAnisotropy; only the proof pattern is reused, not its ternary statement. Recomputed residue tables and exact symbolic order/Gram/inverse checks support implementation. Hosted Lean and independent bound acceptance remain pending. Evidence: verification/descent-pattern-source.json; verification/check_order.py; verification/check_division.py.

## Validation

Static nine-source closure, exact residue/Gram/adjoint symbolic checks and audit-history controls are run separately. No local Lean compilation or build is permitted or performed. Hosted checking and independent source binding remain pending. No full arithmetic theorem or abelian-scheme construction is claimed.
