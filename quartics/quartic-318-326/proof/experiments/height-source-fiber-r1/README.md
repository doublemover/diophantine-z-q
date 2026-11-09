# Actual rational contact-fiber producer

Status: all three sources passed strict Lean 4.35.0 checks and the private-inclusive recursive audit of 43 declarations. A bounded non-author consuming review is pending. These sources are outside the accepted progress manifest. No unconditional height theorem is asserted.

The three modules construct the following objects, without an existence-of-a-point hypothesis:

1. For every four-tuple of rational coefficients, take a maximal residue field of the actual tensor product of the four quadratic root algebras. This algebra has rank sixteen, so the residue field is a number field of degree at most sixteen. Specialization is allowed to collapse squareclasses; generic independence is never assumed at a rational value.
2. Specialize the original source order at the supplied rational contact coordinate t. Compose the existing exact coefficient-base-change map with the residue-field map, then apply Spec and the original full finite-chart embedding. The result is a point on the original proper contact model, with an exact equality of its composite with the original modelMap and the rational coordinate point of the original projective line.
3. Every field-valued point of the nonbranch four-root fiber belongs to the free, transitive orbit of the sixteen actual sign maps. This does not require an algebraically closed field.
4. At t = 32u/v, the literal five-form nonvanishing assumptions imply nonvanishing of all four root coefficients and of all four chosen roots. The infinity contact is accounted for by v being nonzero.

The result works for every rational unit twist tuple, including the independently specified source tuple. It does not prove that a chosen twist is the Shimura/PEL curve, construct a level-three marking, or pull back a universal abelian surface.

## Exact application contract

- Source theorems: the existing FourRootOrder318 finite_free, rank_sixteen and baseChange; FourRootSignBaseChange318 coefficientMap and coefficientMap_generator; SourceGlobalAffine318 chartEmbedding and chartEmbedding_over_contact_line; Mathlib maximal-ideal existence, quotient field/finiteness and surjective linear-map dimension comparison. Pinned Mathlib: 56a005855ea17e0b0958f73ec801ae140b0a1679.
- Required domain: every rational t and every four-tuple of nonzero rational twist constants. This includes all noncontact primitive homogeneous pairs through t = 32u/v, rather than only generic transcendental t or squareclass-independent specializations.
- Constructed domain: the original polynomial source order specialized by the actual evaluation map Q[t] to Q, followed by its actual maximal residue-field quotient. No unrelated field or root tuple is substituted.
- Coefficients: Q throughout the source construction; the rational-fiber residue field is a finite extension of Q. No assertion of an integral arithmetic model is made.
- Maps and direction: original source order to specialized four-root order to its maximal residue field; Spec reverses these maps, followed by the existing source chart embedding. The modelMap square is checked as an equality of Scheme morphisms.
- Normalization: the metric coordinate is t = 32u/v, not u/v. The four finite branch coordinates are 0, 32, 76832 and -343; the fifth is infinity.
- Index coverage and exceptional cases: all four root indices are checked. Coefficients can be square or squareclass-dependent, and the degree can decrease. The field construction itself also exists at branch values; the literal avoidance theorem alone asserts nonzero roots.
- Downstream object: the output is a point of ContactProjectiveModel318.model with its actual modelMap, not a point of an abstract isomorphic curve. It is not yet a point of the quaternionic fine moduli scheme.
- Acceptance and dependency effects: no accepted source or previous application contract is changed. New sources remain experimental and require strict checking and separate source review. Earlier classical fiber/model arguments are preserved as history, not relabeled as a new arithmetic gap.

## Degree boundary

The bound sixteen belongs only to this contact-cover point field. The classical full principal-level-three PEL fiber has a separate degree-dividing-576 argument. Neither its level marking nor its normal splitting field is supplied here. A finite degree bound alone does not prove good reduction or ramification support. No field in CMInputs, NonCMInputs or MetricSections is silently replaced by this field.

See REALIZATION-STATUS.md for the remaining direct consumers and exact proof boundary.

## Verification

Exact source hashes, strict-check logs, the private-inclusive audit source/log, and required predecessor source pins are frozen under verification/. The three source checks used -j1 -M6144 -Ddebug.skipKernelTC=false and only the three standard allowed axioms. Run bash verify.sh /absolute/output/path with Lean 4.35.0 and LEAN_PATH set to the verified predecessor and pinned upstream libraries. This rechecks this packet, not the full repository.
