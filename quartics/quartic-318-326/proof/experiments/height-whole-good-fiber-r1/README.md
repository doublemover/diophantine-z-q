# Whole arithmetic fibers of the good-contact order

Draft only. Hosted Lean checking and independent acceptance are pending. No local Lean compilation was run. The accepted progress snapshot is unchanged.

This packet copies the three modules of `height-good-chart-reduced-r2` unchanged. Its two new modules construct the missing whole affine coefficient-base fiber reducedness, rather than infer it from individual field-valued fibers over the punctured polynomial line.

`EtaleQuotientReduced318` proves reducedness of B/(I B) for a flat etale A-algebra B when A/I is a domain. The proof uses the canonical actual equivalence B/(I B) to (A/I) tensor over A with B, then the previously constructed generic-fiber injection proof.

`IntegralContactWholeFiber318` proves that the original denominator, the product of the four literal factors at 0, 32, 76832, -343, is monic over any coefficient ring. Every power of it has leading coefficient 1, so its powers are disjoint from every extended prime coefficient ideal. Therefore the actual quotient of Base R by a prime coefficient ideal is a domain, by the actual prime localization theorem. The original finite-free etale order over that base has a reduced whole coefficient fiber. The principal-parameter specialization names exactly the quotient required by the localized-base tensor bridge.

This covers the entire noncontact affine chart, for every prime coefficient ideal when 2 and the chosen twists are units. It allows collided contacts after reduction because their common locus remains excluded by the same denominator. It does not construct the missing contact neighborhoods, infinity, a model in characteristic 2 or with nonunit twists, a complete semistable model, or all-place coverage. The local DVR and differential-frame inputs to the vertical tensor criterion are not claimed here. An application to actual local frames is subsequent work. No input identifies a merely related ring with the original order: the theorem concludes reducedness of its actual quotient.

## Application obligations

1. Objects: R is the actual coefficient ring, Base R the original denominator localization of R[X], and Order R c the original four-root order. The resulting fiber is its actual quotient by I mapped along algebraMap R (Order R c).
2. Indices: all prime ideals I of R are included under the explicit unit hypotheses; all four original contacts remain in the denominator and order. The argument does not omit collided odd-characteristic contacts within the stated denominator open.
3. Domain: I is prime, all four twists are units, and 2 is a unit for order-fiber reducedness. No assumption that R itself or the cover is a domain is required. Excluded contact loci and characteristic 2 are not silently covered.
4. Coefficients: the same prime ideal and the same principal base parameter are mapped through R, R[X], Base R and Order R c. No rational-prime normalization or change of ramification index occurs.
5. Local conditions: the base quotient domain is constructed from prime polynomial extension and denominator disjointness; the order fiber reducedness is constructed from its actual free etale producer. Neither is assumed. No DVR/frame existence is fabricated.
6. Transition maps: polynomial inclusion and localization extend the same prime ideal. The scalar tower proves equality of successive ideal maps with the actual R-to-order ideal map. The canonical quotient/tensor equivalence and actual injective generic tensor inclusion provide reducedness.
7. Identity: the conclusion is IsReduced of the whole arithmetic quotient of the exact original noncontact order, and its principal specialization is literally the quotient used by LocalizedBaseTensorSections318. Individual punctured-line field fibers are not substituted for it.
8. Consumers: this supplies the previously missing reduced affine input for the localized-base vertical tensor implication on the good-contact chart. Other local DVR/frame, bad-contact and complete-model obligations remain open. Prior packets and accepted snapshot are untouched.
9. Validation: exact copied-source and primary theorem pins, source/readme/consumer bindings, static import closure and audit-history tests are recorded. Hosted kernel checking and independent acceptance are pending. No whole arithmetic theorem is claimed.
