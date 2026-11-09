# Algebraic etale certificate on the original arithmetic open

Status: uncompiled hosted-CI candidate. Structural checks and source review
are not kernel acceptance. No local Lean build was run.

An explicit polynomial Bezout identity for the unchanged universal quartic
and its derivative gives a genuine standard-etale presentation away from the
original j(j-1728). The exact base-preserving Laurent equivalence maps its
inverted element to the original moduli-source localization, and the full
localization equivalence transfers algebraic etaleness to that source ring.
The entire scalar map is checked to equal the actual j pullback, rather than
the unrelated original T action on the same Laurent ring. Applying Spec and
the original scheme squares proves etaleness of the actual projective j map
restricted to the original arithmetic open, including its rational moduli
scheme interpretation. No analytic local-order inference is used here.

The open excludes both entire elliptic fibers. It is not claimed to be the
maximal etale locus, and the unramified -27 point above zero is not declared
ramified. A full ramification-divisor identity and general quotient/PEL inputs
remain separate, as does full318/326 arithmetic completion. Rational inversion
of3 does not give a false integral extension through characteristic3.

This superset also retains exact failed hosted evidence and repairs the two
reported RationalPairLocalMaps category-projection/unit-reduction failures.
All other82 predecessor source files are byte-for-byte unchanged.

## Exact application contract

1. Original polynomial and branch coefficient. Required: An etale argument must use the exact universal quartic and the exact original base j coordinate. Constructed: branchPolynomial is the original coefficient X*(X-1728) in Base=Q[j]; the outer polynomial is the unchanged ThreeJMonicAlgebra318.polynomial. Application: No alternate quartic, scaling of the root or abstract separable extension replaces the original Laurent presentation.

2. Explicit algebraic Bezout certificate. Required: Analytic derivative nonvanishing cannot substitute for a scheme-level unramifiedness input. Constructed: integer_bezout proves derivative(p)*A+p*B=3^24*C(j(j-1728))^2 with fully written polynomial A,B. Application: The equality is discharged by polynomial derivative identities and ring normalization in the original nested polynomial ring. It is an identity over Q and retains the exact original coefficients. Symbolic expansion was used only as an independent diagnostic.

3. Verified rational scalar normalization. Required: The standard-etale condition needs the actual branch power, not an unspecified nonzero scalar multiple. Constructed: scalar is the Q-algebra image of1/3^24 and scalar_identity proves3^24*scalar=1 in the original nested polynomial ring. Application: Multiplying the explicit Bezout identity by scalar supplies the full StandardEtalePair condition with exponent2. This rational inversion is not an extension through characteristic3.

4. Actual standard-etale localization. Required: The monic-presentation theorem must receive all hypotheses and identify its resulting ring. Constructed: pair has the exact monic p, g=C(branchPolynomial) and the explicit Bezout witness. LocalModel is Localization.Away of the image of g in AdjoinRoot p. Application: The exact pinned pair.equivAwayAdjoinRoot identifies the standard-etale algebra with LocalModel, supplying Algebra.Etale Base LocalModel without using complex point data.

5. Entire localization equivalence. Required: The standard-etale ring must be identified with the original moduli source open, not merely a ring with the same fibers. Constructed: localizing_element proves the existing baseCoordinateEquiv sends AdjoinRoot.mk p(Cg) to the exact original deleted=jLaurent*(jLaurent-1728). powers_map identifies the whole inverted submonoids. Application: IsLocalization.ringEquivOfRingEquiv gives a two-sided ring equivalence, upgraded to a Base-algebra equivalence by explicit coefficient compatibility and scalar towers. It transfers etaleness to the entire original rational source open.

6. Exact j scalar map and scheme etaleness. Required: The Q[j] action on the Laurent ring can differ from its original T action; etaleness must use the j pullback. Constructed: The local Laurent Base action is explicitly jAlgebra. openAlgebra is its localization extension, and actual_scalar_map proves this entire coefficient map equals aeval of the same original source j. Application: rationalJ_etale applies the scheme Spec-map criterion to that verified map, not an arbitrary inferred Q[T] algebra action.

7. Original projective and arithmetic consumers. Required: The algebraic certificate must concern the unchanged global j map and the actual rational arithmetic model. Constructed: original_restriction_etale uses the exact global_j_square. arithmetic_restriction_etale composes the inverse of the proved rational moduli scheme isomorphism with that same restriction. Application: Both original source opens and their scheme embeddings are unchanged. The resulting algebraic etale statement is independent of the analytic local-order certificates, while all previous compact and marked-point identities remain available.

8. Narrow hosted-CI repair and evidence. Required: The exact reported RationalPairLocalMaps failure must be repaired without changing tested evidence or claiming broader proof acceptance. Constructed: The mapped denominator-unit proof now explicitly unfolds y and iy. The overlap proof explicitly exposes both typed aeval ring maps before rewriting hn/hd through category morphism projections. Application: Only RationalPairLocalMaps318 changes among83 predecessors;82 source bytes are inherited unchanged. Exact run42579994089 on cee0c58 RESULT/log are retained separately, along with the two repair descriptions.

9. Validation and remaining ramification boundary. Required: Algebraic etaleness of this open is not yet an equality of full scheme ramification divisors. Constructed: Two new modules and one narrow predecessor repair form85 sources. Structural/hash/application and audit checks run without local Lean; hosted checking and non-author review remain necessary. Application: The open excludes both full elliptic fibers, so this does not claim that -27 is algebraically ramified or that this is the maximal etale locus. Full divisor identities, general quotient/PEL inputs and full318/326 arithmetic completion remain separate.

