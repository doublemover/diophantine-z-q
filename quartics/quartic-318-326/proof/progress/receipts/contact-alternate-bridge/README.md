# Actual selected-contact leaf assembly

This frozen packet decodes the literal common detector leaves into the inputs and comparisons used by the split logarithm packets.

## Interfaces

- `ContactLeafData318.inputs0_bounds`, `inputs1_bounds`, `inputs2_bounds`: each actual source input list implies one common `LeafBounds` object, with all literal weights unchanged.
- `ContactLeafData318.source_tests`: extracts square-root depths 4,13,13,13 from leaves10–13 for L_i-conj(rawRatio_i); depth4 for L1-beta; depth13 for the exact source Lucas polynomial.
- `ContactOppositeData318.source_alternate_inputs`: selected H depth8 and common literal leaves imply nonzero shift, unit D at the opposite actual split embedding, opposite fV depth at least2, and positive alternate deltas. Opposite orientation and even V depth are derived, not supplied.
- `source_mapped_comparisons`, `source_mapped_beta`, `source_mapped_lucas`: the exact comparisons in Qp, using the selected embedding for primary variables and precisely its conjugate for alternate variables.
- `RawSelectedLeafData318.source_selected0`, `source_selected1`, `source_selected2`: the original literal rational root contact chooses an actual split root/orientation and returns the positive scale margin, selected H depth8, and all common leaf bounds. No split root or scale-valuation finiteness is supplied.

The exact beta is 3723+14892*w0+14892*w118. The exact Lucas expression is L3^2-L2*(L2-2)*L3*L4+(L2-2)^2*L4^2-1, in the source's one-based variable names. It is not replaced by a simpler product relation.

## Boundary and verification

The raw selected-contact wrappers retain the prime, bad-prime exclusions (contactModulus,17,41), the literal source assignment, and the positive odd valuation of one of the actual rational root contacts. Applying analytic logarithm theorems additionally requires p>=19; this follows from the separate full S_bad exclusion, not from contactModulus alone (which omits13).

The coherent integer-label/log-ratio and final congruence assembly is separate work. This packet provides its exact source-local inputs without assuming that stored approximants are exact logarithm ratios.

Fresh `bash run.sh` replay strictly kernel-checks all three modules with -Ddebug.skipKernelTC=false. Recursive audit: 42 declarations, three modules, only propext, Classical.choice, Quot.sound. Sources and direct project dependencies are hash-bound. No repository or Git changes made by this packet.
