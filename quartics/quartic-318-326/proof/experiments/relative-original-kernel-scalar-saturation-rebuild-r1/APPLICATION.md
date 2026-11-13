# Application contract

## Full quotient action
Requires: Scalar multiplication must preserve the actual tensor-kernel and full defining ideal.
Constructs: Transport scalar multiplication through ProjectiveKernelParameter.points, with ambient quotient equality.
Justification: The kernel is a submodule; no projective kernel is needed.

## Original coordinate-one slice
Requires: A map from the actual full kernel quotient, not a reduced point-space surrogate.
Constructs: Kill every original equation in the literal slice quotient and lift its full ideal.
Justification: Ideal.span_le and Quotient.lift establish the exact algebra map and coordinate one.

## Actual normalization identity
Requires: The normalized point must recover the same original principal point including its unit.
Constructs: Use backward_include and full quotient extensionality.
Justification: The scalar is precisely the first component of the old normalization equivalence.

## Arbitrary original sections
Requires: Scaling law must hold on the old arbitrary line, without H1 vanishing.
Constructs: Apply the actual kernel-to-section linear equivalence and existing whole-zero unit theorem.
Justification: Full zero scheme equality includes nilpotents and multiplicities.

## Named coefficient transport
Requires: The R-action and actual pullback line must match the universal specialization.
Constructs: Explicit f.toAlgebra telescope, rational ring map, coefficient equality and zeroIso.
Justification: No instance with a hidden uninferrable map is registered; old coefficient-congruence method credited.

## All-ring unit saturation
Requires: All coefficient rings, including nonreduced ones, and true units must be covered.
Constructs: Original factor iff for a principal point and its coordinate-one original slice point.
Justification: Whole-zero equality supplies both directions; nonunit scaling is explicitly excluded.

## Literal projection
Requires: The scheme projection used downstream must be the original Laurent normalization.
Constructs: Identify coefficient map and its Spec point formula.
Justification: Contravariant composition matches the second normalization component.

## All-prime open descent
Requires: Equality of opens requires every actual prime, not only rational points.
Constructs: Generic open field-test extensionality via native Spec residue fields, then actual slice locus.
Justification: Every principal point is tested over its residue field; exact ring maps install its coefficient action.

## Boundary and consumers
Requires: Do not infer overlap gluing, global quotient effectivity or Jacobian representation.
Constructs: Only a genuine open on each actual slice and its exact principal preimage are supplied.
Justification: Full overlap agreement/global assembly remain next; raw norm factor 8 remains unchanged.
