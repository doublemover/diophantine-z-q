# original-five-kernel-norm-equivalence-r8

DRAFT SOURCE REPAIR; HOSTED LEAN PENDING. No independent acceptance or arithmetic theorem claim.

Revision of `original-five-kernel-norm-equivalence-r7` at `56773da3e1a8045d885059ae17053fcbf0af6067`.

Use fully qualified ring-isomorphism conversion in local notation and parenthesized notation operands for field projection, preserving the exact original full-open exponential/logarithm and dual-coordinate maps.

## Objects

Retain the same ring R, scheme X, structure p, affine open V, original sections on V and the full inverse-image thickening open. E is still the RingEquiv of sectionsIso R p V and B the RingEquiv of baseIso V; no substitute equivalence is constructed.

## Coefficient actions

The local-base section coefficients and thickened dual-ring coefficients are unchanged. E and B have the same conversion operation and argument as before, written with its canonical qualified name CategoryTheory.Iso.commRingCatIsoToRingEquiv.

## Exact maps

The original exp remains Units.map E.symm applied to the same affine exponential after B. The log remains B.symm after the affine logarithm of Units.map E. Coefficient, epsilon and reduction squares use the same native original maps. Dual coordinates retain the same SquareZeroRingLift congruence followed by the same affine equivalence and E.symm.

## Native application and diagnosis

Hosted OriginalThickenedOpenSections318 passed. OriginalOpenUnitLogarithm318 then fails before elaboration because projection syntax in notation has no quot_precheck support, and E.symm/B.symm are parsed as dotted identifiers. Qualified prefix application avoids that notation-precheck projection; (E).symm and related parenthesized projections operate on the expanded term rather than an identifier namespace. No check is disabled. OriginalOpenDualCoordinates318 has identical E/B syntax and receives the identical limited correction proactively; this later module was not reached by the hosted run.

## Index and full-open coverage

All original sections of the full affine open V, all units of the entire inverse-image thickened open, and all full dual-ring elements remain quantified. Restriction and norm domains are unchanged; no generic-only or reduced-unit-only substitute is introduced.

## Local hypotheses

The original IsAffine V.toScheme hypothesis and all ring/scheme data remain exactly as stated. No extra invertibility, trivialization, normality or splitness assumption is introduced. The inherited original reduction condition in exp_log is unchanged.

## Downstream consumers

TwoOpenUnitCocycleExt318 and OriginalHOnePointedSurjection318 consume the same original logarithm/exponential correspondence. OriginalOpenDualCoordinates318 and the later actual thickened norm modules consume the same literal coefficient and epsilon maps; only notation parsing is corrected.

## Evidence and limitations

The exact hosted first failure, before source, result record and bounded patch are retained. Every other root Lean module is byte-identical to its published predecessor. No imports, heartbeat limits, admitted axioms, accepted baseline or artifact-cache policy change. Source inspection is not a Lean pass; fresh strict compilation, axiom audit and independent review remain pending. The complete concrete public targets and their actual downstream consumers must elaborate in hosted CI.
