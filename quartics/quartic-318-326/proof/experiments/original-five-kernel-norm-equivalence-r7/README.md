# original-five-kernel-norm-equivalence-r7

DRAFT SOURCE REPAIR; HOSTED LEAN PENDING. No independent acceptance or arithmetic theorem claim.

Revision of `original-five-kernel-norm-equivalence-r6` at `4d85d68746c3729658dd5f85869f7dd4fc2b505f`.

Preserve the original coefficient, reduction and epsilon squares by transporting appLE together with its dependent open-inclusion proof and normalizing the preimage of top.

## Objects

The same ring R, scheme X, structure map p, open V, thickening R p and local thickening on V are retained. baseIso, sectionsIso and reduce have unchanged definitions.

## Coefficient actions

All maps remain maps of CommRingCat sections over the original arbitrary CommRing R. The coefficient projection and the original dual-number epsilon are unchanged.

## Exact transition maps

appLE_of_eq equates appLE for equal scheme maps while abstracting both inclusion proofs. inclusion_fst and reduction_map supply exactly the original composite equalities. preimage_top normalizes only the full open, not a smaller domain.

## Native theorem application

The new private helper is proved solely by subst g and rfl. appLE_comp_appLE is applied in its native contravariant direction, then helper equality replaces the map and dependent proof together. epsilon_naturality remains the exact source theorem; preimage_top closes its top-open presentation mismatch.

## Index and open coverage

The entire inverse-image open π(R,p) preimage V and all sections on it remain in each statement. The theorem still ranges over every original open V.

## Local hypotheses

No new hypotheses are added; the inherited open-immersion inclusion and actual pullback construction are unchanged.

## Downstream consumers

OriginalOpenDualCoordinates318, OriginalOpenUnitLogarithm318 and the original norm/trace comparison modules consume the same full-open coefficient, reduction and epsilon equations.

## Scope and evidence

The exact first failure from hosted run 43344479993 is retained with the before source and bounded patch. All other root Lean sources are byte-identical to the predecessor; the original packet remains intact. New source hashes describe the draft rather than a passed check. Kernel checking, recursive axiom audit, later module success and independent source acceptance remain pending. This packet adds no admissions, placeholder axioms, resource changes or accepted-cache modifications.
