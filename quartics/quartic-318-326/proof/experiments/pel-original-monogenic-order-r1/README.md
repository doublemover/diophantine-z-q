# Original monogenic candidate order

Reconstructed from the exact available r112/r113 source frontier, not from conversation-only completion reports.

`PELOriginalMonogenicOrder318.exists_original_order_equiv` produces one nonzero polynomial base denominator, a monic separable polynomial equal to the original primitive minimal equation in the same rational coordinates, the original primitive generator as a regular source function, and an actual ring equivalence from AdjoinRoot of that polynomial to the ENTIRE original candidate chart localization. It sends the quotient root to that exact function and fixes every original localized base coefficient.

The source of surjectivity is the previously constructed whole-order polynomial generation. `ActualPrimitiveRestriction318` proves that it survives restriction by an additional BASE denominator, using the exact original Cartesian coefficient square, all original finite algebra generators, and the whole source localization. `ActualPrimitiveQuotient318` proves injectivity: map any annihilating polynomial into the original projected-coordinate field, use the actual minimal-polynomial divisibility theorem, then descend divisibility of a monic polynomial through the injective coefficient map. No field equality is used as a substitute for order equality.

All denominators are in the same two projected base coordinates. The field generator, minimal equation and original source-to-field embedding are unchanged. Monicity and derivative Bezout separability survive coefficient restriction. The resulting isomorphism is not a chosen factor or component and does not omit any point of the localized candidate.

Remaining: transport the actual candidate complex fibers through this base-preserving equivalence; identify the independently topologized root-locus charts with the original analytic image; prove global sheet selection, continuation/density and whole-image equality; then rational descent and subsequent PEL/Jacobian identification. None is inferred from the order equivalence alone.

Status: source draft, pending independent review and hosted Lean checking. No local Lean build, replay, profiling, or kernel audit has run. Static source/dependency checks do not establish Lean elaboration or theorem completion.
