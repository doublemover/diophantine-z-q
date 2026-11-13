# original-finite-quotient-reconstruction-r59

DRAFT SOURCE REPAIR; HOSTED LEAN PENDING. No independent acceptance or arithmetic theorem claim.

Revision of `original-finite-quotient-reconstruction-r58` at `4d85d68746c3729658dd5f85869f7dd4fc2b505f`.

Install the exact native coefficient algebra on the affine polynomial-chart function field inside base_coefficient, preserving the existing coefficient equality and all Cartesian consumers.

## Objects

The same polynomial ring R = Polynomial Q, projective line B, integral Y, dominant integral p, domain A, open chart j, map f and actual pullback square H remain. No alternative chart or field is selected.

## Coefficient actions

The added proof-local Algebra R (Spec R).functionField is exactly AlgebraicGeometry.instAlgebraCarrierFunctionFieldSpec, the instance already used in ActualOpenFractionField318.genericAlgEquiv and OriginalProjectiveFunctionCoordinate318.coefficient.

## Exact transition maps

The original genericEquiv and genericAlgEquiv, canonical projective κ, and ring map f are unchanged. The local instance lets .commutes elaborate with its declared affine target action.

## Native theorem application

base_coefficient still applies injectivity of the original genericEquiv and composes coefficient q with genericAlgEquiv.commutes q in the same direction. The single added instance is proof-local and not a new global registration.

## Index and open coverage

Every polynomial q remains quantified. No coefficient subring, localization, or finite subset replaces the original full polynomial ring.

## Local hypotheses

The integral, dominant, domain and open-immersion assumptions, plus actual Cartesian square H, are unchanged. No extra assumption is added.

## Downstream consumers

coefficient_square, coefficient_tower and coefficient_integral retain their statements. OriginalCartesianNormalChart318 remains the unchanged immediate downstream consumer, with its separate possible elaboration issues not claimed repaired.

## Scope and evidence

The exact first failure from hosted run 43344479993 is retained with the before source and bounded patch. All other root Lean sources are byte-identical to the predecessor; the original packet remains intact. New source hashes describe the draft rather than a passed check. Kernel checking, recursive axiom audit, later module success and independent source acceptance remain pending. This packet adds no admissions, placeholder axioms, resource changes or accepted-cache modifications.
