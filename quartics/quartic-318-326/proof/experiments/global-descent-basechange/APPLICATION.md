# Application contract

1. **Source requirements.** OriginalGlobalBaseUnit318 requires the original affine, flat, surjective scheme arrow and actual base lines. OriginalGlobalLineMapDescent318 consumes exactly its unit, exact covering identity and independently proved pullback faithfulness. Base change requires both covering arrows affine, flat and surjective, plus a displayed commuting square, not a cartesian square.

2. **Constructed objects.** The original Line objects and OriginalSchemeDescentData318.Datum are unchanged. Arbitrary original base-line maps are descended by conjugating reconstruction maps through the actual base unit. The changed object is the original datum pulled back along a, and the candidate base object is the literal b-pullback of the original reconstructed line.

3. **Coverage.** Every original base line and every compatible sheaf map is quantified. Both bases and covering schemes are arbitrary schemes subject only to the stated covering-arrow hypotheses. The previously proved full affine-basis assembly supplies their whole sheaves, not only affine chart values. Non-affine covering arrows remain outside this packet.

4. **Transition directions.** The canonical square comparison goes from a-pullback of f-pullback to g-pullback of b-pullback. Its inverse, followed by a-pullback of the original reconstruction comparison and the inverse new reconstruction comparison, gives the exact covering iso used to descend the new base comparison. OriginalCanonicalDescent318 proves the actual double compatibility for both directions.

5. **Hypothesis checks.** Global map descent is applied only to canonical original data of the two specified original base lines and the proved compatible covering hom. Its inverse compatibility is derived from that actual isomorphism. No new cocycle, scalar, isomorphism, or naturality assertion is assumed. Both affine/flat/surjective sets of instances are explicit in each consumer.

6. **Consumer identity.** The new comparison is an iso from literal b-pullback of the old globally reconstructed line to the unchanged reconstruction of the original changed datum. comparison_cover and comparison_unique identify it on the entire original cover. The natural transformation component is this same iso, not an abstract choice from an equivalence.

7. **Scalars and normalization.** descend_cover recovers the supplied covering hom exactly. The comparison retains the original coverComparison inverse and both original reconstruction maps, so no scalar or arbitrary endpoint normalization can be discarded. Naturality follows from these literal equations and faithful pullback.

8. **Downstream boundary.** This extends the old affine-spectrum base-change comparison to arbitrary base schemes and supplies the actual functorial interface for refinement. Mixed-cover refinement, non-affine covering morphisms, general fppf stack assembly, represented Picard/Jacobian and the arithmetic theorem remain separate.

9. **Evidence and acceptance.** The 165 producer sources are byte-for-byte copies of affine-global-categorical-equivalence-r2, including bounded hosted timeout diagnostics. Five new sources require hosted Lean elaboration, strict recursive axiom audit and independently authored review. Static import/hash and audit-history checks are not mathematical proof or acceptance. No local Lean compile was run and no global acceptance register was modified.
