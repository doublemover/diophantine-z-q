# Independent geometry propagation review: normal-infinity trace r4

Reviewer: lean_review_resume (internal model review, distinct from geometry_repair_resume and PEL integrator).
Base commit: 4d85d68746c3729658dd5f85869f7dd4fc2b505f. Hosted evidence: run43344479993.
Target: quartics/quartic-318-326/proof/experiments/height-original-normal-infinity-trace-r4, predecessor r3.

## Exact changed sources

- IntegralRationalInfinityMap318.lean: b3a37fb56e341a83585bf2a8c887c2b006aecde39b5d9e8ed1307dd99469064d
- IntegralOriginalInfinityEmbedding318.lean: a3286e4829e0a388ef00169d4bdfb1d571effc6f89950b919a3b0961fec35970

Independently read both complete changed sources, exact trace r3/r4 diffs, the geometry failure logs, and relevant defining dependencies/native APIs. Both trace predecessor sources are byte-identical to the geometry predecessor sources reviewed in height-original-ks-lattice-assembly-r6. Both propagated after-sources are byte-identical to geometry r7 and its reviewed hashes. Read arithmetic_repair_resume's independent geometry report; this additional review concerns the trace application and does not impersonate its author.

## Application and consumer check

The rational-map repair uses the existing CommonBase scalar action on the original overlap. mapped_smul expands its algebra map, not another action. RingHom.ext_rat establishes equality on all rational constants, Polynomial.ringHom_ext includes X, localization extensionality covers the entire original denominator localization, and ThreeRootCoordinates318.ringHom_ext covers all three ordered generators. The Presentation denominator is the original product of the three coefficient polynomials. The reciprocal coordinate, signed root ratios, original full field embeddings, and infinity_restriction consumer remain unchanged. No coefficient subset, root subset, scalar factor, or substitute field is introduced.

The open-embedding repair projects opensRange to its underlying set before rewriting the same map. The pinned opensRange definition is the actual map range, and opensRange_comp_of_isIso discards only the leading scheme isomorphism, as required contravariantly by the same ring-equivalence composition. The native localization range equality retains the exact denominator basic open. The local openness instance is the proven localization_equiv_open specialized to the original P,F,A,B,x,e, not a new assumption. Public ringMap/inclusion/chart/polynomial statements and downstream original-gluing, full-intersection and proper-model consumers keep the same maps.

## Dependency variant checked

IntegralOverlapRootGenerators318.lean differs between the trace closure and the geometry closure. The trace copy retains the older native_overlap_generator proof, whereas geometry uses named intermediate carriers with overlap_value and diagnostic markers. I read the difference and compared finiteGenerator, infinityGenerator, actualOverlap_generator and infinityMap_generator. Their public definitions, quantified indices and theorem conclusions agree; the propagated repair consumes the same signed inverse-root formula. The trace dependency is unchanged from trace r3. It may still encounter its own earlier elaboration failure, which this two-file propagation does not claim to fix. InfinityOrderCoordinates318 is supplied by the retained shared baseline rather than a trace root source; no replacement was introduced.

## Verdict

No blocking source-level propagation defect found. These two bound files are suitable for the next hosted trace-r4 replay. No Lean/Lake command or local build ran; no user computer was accessed. Definitional equality/elaboration, kernel checking, recursive axiom audit, unchanged dependency success, and subsequent consumer success remain pending hosted CI. This is not whole-proof acceptance, an accepted application-binding refresh, or a claim of arithmetic theorem completion.
