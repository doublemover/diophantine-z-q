# Exact analytic ramification divisor and algebraic derivative open

Status: uncompiled hosted-CI candidate. Structural checks and bounded source
review are not Lean kernel acceptance. No local Lean build was run.

This stage connects four constructions on the unchanged original j morphism:

- The image of the actual monic quartic derivative is exactly
  S*(T+243)^2*(T^2-486*T-19683) in the original Laurent source ring.
- A genuine standard-etale presentation and coefficient-preserving localization
  equivalence prove that the original scheme map is etale on its derivative
  open. Its range is computed on all rational prime ideals.
- The complete effective analytic ramification divisor on the actual projective
  complex points is2[0]+2[-243]+[243+162*sqrt3]+[243-162*sqrt3]. Every point has
  an original scheme-chart local-degree certificate equal to its coefficient
  plus one. Infinity has coefficient zero. The total degree is six, and literal
  mapPoints pushes it forward to2[infinity]+2[0]+2[1728].
- Evaluation of the original algebraic derivative is invertible exactly where
  the analytic coefficient vanishes on the Laurent chart. The point-27 is
  explicitly included. The divisor is pulled back through the already proved
  original compact modular biholomorphism, retaining the actual cusp identities.

The numerical degree identity uses the exact generic-stalk j pullback algebra,
not the identity action on the same underlying function field. This is not a
claim that a global scheme Cartier/Fitting/different divisor has been identified.
The algebraic etale converse at every omitted prime, the scheme statement at
infinity, general quotient/PEL realization and the full318/326 arithmetic result
remain separate. All85 predecessor sources are byte-for-byte unchanged.

## Exact application contract

1. Exact monic derivative and scalar action. Required: A scheme etale argument must use the original universal quartic over the original coefficient j ring. Constructed: derivativeImage is the image of the derivative of the original polynomial under the existing Base-algebra coordinate equivalence, with Laurent Base action explicitly jAlgebra. Application: derivative_times_parameter and derivative_factorization prove the exact identity delta=S*(T+243)^2*(T^2-486*T-19683). The Laurent unit is retained; no abstract separability or point comparison substitutes for this equality.

2. Actual larger etale open. Required: StandardEtalePair must receive its exact monic polynomial, localization element and Bezout condition. Constructed: The pair uses the unchanged p and g=p.derivative, with witnesses1,0,1. An explicit coefficient-preserving localization equivalence maps its localized AdjoinRoot to Localization.Away derivativeImage in the original Laurent ring. Application: Etaleness transfers along the algebra equivalence and the entire scalar map is identified by actual_scalar_square. original_restriction_etale concerns the unchanged projective scheme morphism composed with the actual open embedding.

3. All-prime coverage of the derivative complement. Required: The localization range must be checked on the entire rational prime spectrum, not only at complex closed points. Constructed: source_open_range uses the localization-away range theorem; source_open_exact identifies it with D(T+243) intersect D(T^2-486*T-19683). Application: The identity T*S=1 makes D(S) the whole spectrum, and basicOpen_pow removes only the multiplicity from the open set. This proves a genuine scheme open and does not claim the converse global non-etale locus.

4. Exact exceptional parameters and multiplicities. Required: The entire elliptic quadratic locus and both cusps must be covered without duplicate or missing points. Constructed: rootPlus and rootMinus are243 plus or minus162*sqrt3 in C. Their distinction, nonzero values, exclusion of-243 and exact factorization of the original D are proved. multiplicity records2 at0,2 at-243 and1 at each root. Application: D_zero_iff exhausts the quadratic roots, and multiplicity_local_degree matches the previously proved finiteOrder at every nonzero finite parameter. The finite origin and reciprocal origin retain their separate cusp certificates.

5. Full analytic divisor on the actual points. Required: A ramification divisor must be attached to the original map and all original source points, rather than a renamed list of numbers. Constructed: ramification is an effective finitely supported function on the genuine base-preserving complex points of the original projective scheme. every_point_local_degree proves a LocalDegreeCertificate with degree coefficient+1 at every point. Application: The inherited certificates give analytic source and target expressions equal to literal mapPoints on a whole coordinate neighborhood. finite_or_infinity exhausts the source. support_exact and degree_six compute the full effective analytic divisor; this is not asserted to be a scheme Cartier or Fitting divisor.

6. Branch pushforward and exact generic degree. Required: Multiplicity pushforward must use the original morphism and degree must use the actual generic-stalk pullback. Constructed: branch_cycle computes Finsupp.mapDomain mapPoints ramification as2[infinity]+2[0]+2[1728]. degree_identity relates the degree-six divisor to the actual degree-four generic field map under its explicit pullbackAlgebra. Application: The zero,1728 and infinity images are proved from original scheme-map chart formulas; no branch labels are assigned by a new point bijection. The numerical genus-zero identity is stated separately from any general Riemann-Hurwitz theorem.

7. Original compact comparison and cusps. Required: The divisor on the compact modular source must be transported by the already constructed comparison, retaining actual cusp identities. Constructed: compactRamification is comapDomain along the original compactPointHomeomorph, already supplied by the actual biholomorphic comparison. compact_coefficient and compact_local_degree preserve every coefficient and local degree. Application: actual_cusp_coefficients gives2 on the original zeroEnd cusp and0 on the original infinityEnd cusp. The inherited canonical q-disc order statements remain unchanged and are not replaced by arbitrary cusp labels.

8. Algebraic and analytic overlap comparison. Required: A larger algebraic etale open must agree with the claimed analytic coefficient and include the simple point over0. Constructed: evaluation is defined for every nonzero complex parameter. evaluation_derivative computes the exact monic derivative; derivative_unit_iff_coefficient_zero proves invertibility iff the actual analytic divisor coefficient vanishes. Application: neg27_in_derivative_open explicitly includes the simple point omitted by the smaller arithmetic open. etaleEvaluation constructs actual localization lifts, with the entire original Laurent evaluation recovered on inclusion. No pointwise statement alone is used to infer scheme etaleness.

9. Preserved evidence and remaining boundary. Required: No uncompiled candidate or bounded source review may be reported as full theorem acceptance. Constructed: All85 predecessor source bytes are unchanged; four new sources form89. Structural hash/import/audit checks and symbolic polynomial diagnostics are run without local Lean. Application: The full analytic effective divisor and the algebraic derivative open are connected, but a global scheme Cartier/Fitting/different divisor identity and the missing quotient/PEL realization still remain. There is no integral extension through characteristic3 and no claim of full318/326 completion. Hosted checking and independent review remain required.

