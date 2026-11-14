# Independent ScalarActualInputs318 source review

No source-level blocker found in the exact reviewed state. This is source/provenance review only, not a hosted candidate pass, kernel acceptance, whole-packet acceptance or declaration audit. No local Lean/Lake or user computer was used. Successor metadata/propagation requires its own review.

## Exact observed bounds and index
Own descent RESULT records ScalarPoleRealDomain passing (4.075s), then ScalarActualInputs failing (3.424s). The log leaves exactly Fin.append(...,0) in both embedding bounds and embedding(chartU h ^ 2) in the half-trace equation. Candidate keeps every integer h and the same original quadratic-field chartU. (0 : Fin4).castAdd 4 is the same first Fin8 coordinate but exposes the left-index form for Fin.append_left; the already compiled CoherentMultiplePrefix.left_point uses this very rule. Parameters remain four label*h followed by four label*(h-1), and constant labels1 evaluate to h. Both exact embeddings and coordinate0 are unchanged; no oval or domain is removed.

## Native embedding-square normalization
The two map_pow facts specialize the original positive/negative ring homs, chartU h and exponent2. They are used on the original re_embedding equality, preserving its half-trace factor1/2. No embedding body is unfolded or alternative scalar action chosen. Existing square positivity, bound1, norm product, and exact_mod_cast arguments remain unchanged; no extra nonzero condition is added.

## Exact consumer and scope
PreparedIntegerSource.scalar_domain consumes the resulting common_bounds h in its detector33 real-part and detector37 norm inequalities for the original DetectorGateWitness assignment. The detector and preserved-slot results elsewhere in this source are unchanged, as are original root signs. This is not a claim of the full arithmetic result. Weighted propagation needs its own RESULT and identical before bytes; the separately available weighted artifact is reviewed at propagation, not substituted for the descent evidence here.

## Exact bindings

- ScalarActualInputs318.lean: before `669eb03d31c5490f7278608a416e1e44ec64d10aa90c044c64c6636759e810f1`; reviewed `dfb2085bb57eab66f47498bfed616a24367c85c373f5b652136d164e7e1701e1`.

The companion manifest binds own logs/RESULTs, Git-pinned predecessor intakes, and primary/consumer evidence. All pre-existing option lines are byte-identical.
