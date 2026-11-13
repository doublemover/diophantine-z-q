# relative-original-normalized-kernel-gluing-r3

DRAFT SOURCE REPAIR; HOSTED LEAN PENDING. No independent acceptance or arithmetic theorem claim.

Revision of `relative-original-normalized-kernel-gluing-r2` at `4d85d68746c3729658dd5f85869f7dd4fc2b505f`.

Transport k and its dependent IsOpenImmersion witness together while proving the unchanged nested-path image inclusion.

## Objects

The same schemes X,Y,Z, open immersions f,g,k, literal composite equality h, module sheaf M and full-open section s are retained.

## Coefficient actions

This is an additive section equality for the unchanged module sheaf M. No coefficient action or scalar is changed.

## Exact transition maps

sectionsEquiv k, PullbackPathComposition318.iso f g k h, sectionPull f, and the ambient presheaf restriction all remain identical. Only the internal proof of k image top <= g image top changes.

## Native theorem application

Replacing rw [← h] by subst k transports the morphism and IsOpenImmersion instance simultaneously. OpenChartSections318.imageLE f g supplies the same inclusion; proof irrelevance identifies the resulting witnesses.

## Index and open coverage

The full image opens k image top and g image top are still used, for every section s on the full pullback open. No domain restriction is introduced.

## Local hypotheses

All three original IsOpenImmersion hypotheses and the literal path h remain. No weakening or extra hypothesis is added.

## Downstream consumers

nested_path and the unchanged section-compatibility, affine-frame, and normalized-kernel gluing modules retain the same original full-open restriction map.

## Scope and evidence

The exact first failure from hosted run 43344479993 is retained with the before source and bounded patch. All other root Lean sources are byte-identical to the predecessor; the original packet remains intact. New source hashes describe the draft rather than a passed check. Kernel checking, recursive axiom audit, later module success and independent source acceptance remain pending. This packet adds no admissions, placeholder axioms, resource changes or accepted-cache modifications.
