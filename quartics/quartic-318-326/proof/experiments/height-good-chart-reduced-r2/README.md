# Reducedness of the actual good-contact open

Draft only. Hosted Lean checking and independent acceptance are pending. No local Lean compilation was run. The accepted progress snapshot is unchanged.

`EtaleFlatReduced318.reduced` proves that a flat etale algebra over a domain is reduced by injecting it into its actual fraction-field tensor product and applying the pinned unramified-over-a-field theorem. The cover need not itself be a domain.

`IntegralContactReduced318` applies this to the actual four-root integral order from `IntegralContactOpenFrame318`, preserving the literal contacts 0, 32, 76832, -343 and unit twists. Its polynomial denominator is nonzero over every coefficient domain, including positive characteristics where contacts collide. The localized base is a domain, the original order is free and etale when 2 is invertible, and its reducedness follows. Every actual field-valued fiber over this noncontact base is reduced; `fiberPresentation` retains all four original coefficients under the canonical tensor-product base-change equivalence.

This does not identify base change along an arbitrary coefficient-ring map with the independently constructed order over the target coefficient ring. It does not yet prove that the whole special fiber over the arithmetic coefficient base is reduced, or that a quotient of a vertical local ring by the actual base uniformizer is reduced. Fibers proved here are over the punctured affine-line base, not the complete curve over the arithmetic base. The contact locus, infinity, characteristic 2, nonunit twists, semistable model construction, DVR identification, and complete place coverage remain open. In odd characteristic, collided contacts are still excluded by the actual denominator open; no claim is made about their missing neighborhoods.

The copied frame module is byte-identical to the versioned `height-global-open-sections-r3` repair and awaits its hosted check. No failed predecessor bytes are overwritten.

## Application obligations

1. Objects: the actual coefficient domain R, Base R and Order R c, and the tensor fiber K tensor over Base R with Order R c. No replacement by a connected component or fraction field of the cover.
2. Indices: all four contact indices remain in the defining product and four-root order. Fiber reducedness quantifies over every field K and every Base R algebra structure on it.
3. Domain: R is a domain, twists are units, and 2 is invertible for the order and fiber conclusions. These hypotheses do not cover all arithmetic places or the omitted contact neighborhoods.
4. Coefficients: original integer contacts and unit twists are mapped through R[X], Base R and the chosen field K. No rational-prime or ramification normalization occurs.
5. Local conditions: reducedness is concluded, not assumed. The base is a domain by localization at a proved nonzero polynomial; freeness and etaleness come from the actual four-root producer.
6. Transition maps: reducedness descends through the injective actual includeRight map into the generic etale tensor algebra. The fiber presentation is the established FourRootOrder318.baseChange equivalence, in its original direction.
7. Identity: the conclusions name the exact original Order R c and its tensor-product Fiber, not rings having merely isomorphic-looking equations. No unproved identification with vertical quotient rings is used downstream.
8. Consumers: this supplies a good-open reducedness prerequisite for later special-fiber/localization comparison. ReducedBaseTensorSections318 is not applied because its actual reduced quotient and DVR inputs have not been constructed here.
9. Validation: exact source and consumer hashes, unchanged predecessor pins, pinned upstream theorem source, strict import closure, and structural audit self-tests are recorded. Hosted kernel checking and independent acceptance remain pending; no whole arithmetic theorem claim.

## Producer repair r2

The frame producer is propagated byte-for-byte from global-open r3 after hosted run 42574563881 rejected custom scalar-action instances in global-open r2. The generic reducedness proof and actual-order/fiber conclusions are unchanged. The prior reducedness packet remains immutable and was never hosted-checked.
