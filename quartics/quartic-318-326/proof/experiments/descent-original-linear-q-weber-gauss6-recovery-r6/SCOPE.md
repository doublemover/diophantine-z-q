# Exact Gauss6 r6: explicit beta targets for local chart representatives

The exact first five modules compiled in official r5 and audited
133 declarations. Only GaussValuation failed. In primitive_chart_pair,
Lean cannot use the local let values a,b as rewrite lemmas. The two
generic field equalities and the two corresponding residue hypotheses
now spell the same element representation by a literal typed change,
then apply the original compiled element_map/mul_element equations
and the unchanged common-scalar argument. This addresses all three
reported lines and the simultaneous b counterpart. No statement,
chart structure, valuation, or public scope changes. Other bytes,
including the independently sufficient Translation7 prefix, are exact.

The official r5 source, complete inventory, ZIP, log and prior
audit are bound; new terminal acceptance is not asserted.
No local Lean, dispatch, push, or broader source change.
