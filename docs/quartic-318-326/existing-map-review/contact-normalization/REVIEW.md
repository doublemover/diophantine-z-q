# Retrospective audit of the published contact maps

## Decision and fixed target

**Accept the bounded field, affine-ring, affine-Scheme, fraction-field and actual normalization-chart equivalences at commit dea5d91b63e43d5f3ba9874c64463a0f28ff934b. Require one prose scope correction: root-sign flips are called inertia flips in a packet README.** No false isomorphism, missing inverse or replacement of an actual normalization by an unrelated model was found in the source chain read here.

This is a non-author source/argument audit by `/root/restart_hodge_gluing` of the contact producer's existing work. The reviewer authored separate differential/Hodge work consuming some of these charts; that downstream role is disclosed and does not independently validate its own work. Prior bounded reviews are historical evidence, not a new independent whole-proof validation. This pass reads the concrete definitions, relations, maps, inverse proofs and consumers, and independently checks all four rational coordinate changes. It does not rerun Lean, repeat a full axiom audit, or accept the complete 318/326 theorem. No shared source or manuscript was edited.

`BINDINGS.json` freezes the exact source/prose files and confirms equality to the specified Git commit. It also binds the locally read Mathlib closure interface and its package commit. `coordinate-check.json` records an independent exact-rational calculation from the actual Lean coefficient declarations, not a numerical fit or a theorem-name check.

## 1. The infinity field map really is invertible

The original carrier is `KummerTensorField318.Raw (SourceKummerField318.parameter c)` for every `c : Fin 4 → Qˣ`, with roots y_i satisfying y_i²=c_i(t−a_i), a=(0,32,76832,−343). Nonempty products of distinct linear factors are nonsquares in Q(t), even with arbitrary nonzero constant twists. The source tensor algebra is identified with an iterated quadratic field, of degree 16 over this particular Q(t).

The infinity carrier is the three-root tensor algebra over a *different embedding* of the rational function field. Its coordinate is u=c₀/y₀, its roots are r_j=y_(j+1)/y₀, and

- u²=c₀/t;
- r_j²=(c_(j+1)/c₀)(1−a_(j+1)u²/c₀);
- t=c₀/u², y₀=c₀/u, y_(j+1)=(c₀/u)r_j.

`InfinityFieldCoordinates318` proves the nonzero conditions used in these inversions. It proves u transcendental by recovering transcendental t, so `coordinateField` genuinely embeds Q(u). Distinct nonzero squared contact roots give the three-root field, including when a quadratic polynomial splits over the constant field: squarefreeness, not irreducibility of each polynomial over Q, supplies independence.

`InfinityFieldMap318` locally installs the u-coordinate algebra structure on the original field and maps the three actual AdjoinRoot generators to the stated ratios. `InfinityFieldEquivalence318` first treats its range as a subfield. It puts u, r_j, rational constants, t and all y_i in that range. Only after rational-function induction proves it contains the *original* Q(t) does it treat the range as an intermediate field over that base. `FourRootGeneration318` proves generation by root-adjunction and tensor induction, not by a dimension comparison. This yields surjectivity; injectivity comes from the constructed source field. `fieldEquiv` is therefore a genuine RingEquiv.

The choice of RingEquiv is correct. It is not asserted to preserve the old t-algebra structure: its separate coordinate theorem states the new rational-function variable maps to u. Degree 8 over Q(u) and degree 16 over Q(t) do not conflict. The concrete fields and schemes use Q in the concrete universe; generic helper universes do not identify two distinct coefficient embeddings by coercion.

## 2. All four cubic/published affine comparisons have inverse maps

For each omitted index i let C_i=product of the other three twist constants, m_i=their contact centroid, and u_i=(630,2058,42,336). The literal cubic ring is Q[t,z]/(z²−C_i product_(j≠i)(t−a_j)). Its map to the published short affine ring is

    t ↦ (u_i²/C_i)x + m_i,    z ↦ (u_i³/C_i)y.

The inverse is

    x ↦ (C_i/u_i²)(t−m_i),    y ↦ (C_i/u_i³)z.

These formulas follow from the actual composition, not from equal j-invariants:

1. `CubicWeierstrassPolynomial318.baseChange` is the invertible affine substitution t↦x/C_i+m_i; its radicand becomes the depressed short polynomial divided by C_i².
2. `UnitRootScaling318.equiv` sends the root to y/C_i and explicitly composes with the inverse unit root scaling in both directions.
3. `AffineCoordinateDomain318.coordinateEquiv` has forward/backward generator maps and both composite identities between the AdjoinRoot and multivariate quotient presentations.
4. `AffineRationalScaling318.equiv` sends the short coordinates to u_i²x,u_i³y and verifies both inverse composites on the two generators.
5. `CubicPublishedScheme318.affineIso` applies contravariant Spec to that same Q-algebra equivalence and proves the actual Q-structure square.

The separate exact-fraction checker reads the declared contacts, constants, scales and coefficients, checks all four cubic polynomial identities coefficient by coefficient, both inverse compositions, the depression identity, the coefficient scalings and nonzero discriminants. The resulting (x coefficient, y coefficient, centroid) triples are:

- i=0: (75, 47250, 25507);
- i=1: (343, 705894, 76489/3);
- i=2: (−1, −42, −311/3);
- i=3: (32, 10752, 76864/3).

This is an affine equivalence over Q. Nothing here turns a finite map of positive degree into an isomorphism, supplies an integral Z-model, or identifies a principal polarization/Jacobian/PEL object. The external assertion that the coefficient list is the published table was not freshly re-researched in this retrospective pass; the literal coefficient and map identities are what this review accepts.

## 3. Fraction fields are the specified fields, not arbitrary copies

`CubicCharacterFraction318.genericFiber` composes actual root base change, the exact complementary-radicand identity, the quadratic presentation equivalence and the field-range equivalence. The carrier is the actual intermediate field generated by the product of the three original roots inside Raw. Its root compatibility theorem and polynomial compatibility theorem identify both parts of the embedding. Freeness makes the order embedding injective.

`TensorFractionField318.fractionRing` first transports the localization at nonzero base elements through an A-algebra equivalence. It then verifies units for every nonzero element of the order, gives a numerator/denominator representation for every target element, and proves equality reflection. Thus the field is the *whole fraction field* of the order under the specified embedding, not merely a containing extension. `PublishedCharacterFraction318.embedding` uses the inverse of the same cubic/published algebra equivalence; `embedding_on_cubic` and the transported IsFractionRing preserve its identity.

The same argument supplies the source and infinity full fraction fields. `InfinityOpenFractionField318` identifies the open order as a localization of the unlocalized order and lifts its embedding using the proved nonzero denominator. The localization then keeps the same original full Raw field as fraction field. No component is selected or substituted.

## 4. The actual global normalization chart comparison is stronger than a field identification

The global source is the relative normalization of the actual unbranched four-root Spec map to the projective contact line, `ContactProjectiveModel318.coverMap c`. The projective line's reusable code name does not make t the modular j-coordinate.

On the reciprocal side, let A=Q[s,1/Q(s)] with Q(s)=product_j (c_(j+1)/c₀)(1−a_(j+1)s). The infinity order is the three-root presentation over Q[u,1/Q(u²/c₀)]. `ReciprocalInfinityBase318` proves the finite substitution s=u²/c₀, by a genuine monic quadratic root presentation, and proves finiteness after localization and adjoining the three roots. The order is normal by its finite-etale domain presentation over the normal localized u-line. Under its specified embedding into Raw, s maps to t⁻¹. Its normality, finiteness over A and full fraction field prove it is precisely the integral closure of A in Raw.

`InfinityGlobalBase318` separately constructs A→the actual unbranched source order. It proves equality of this embedding and the infinity embedding on the *entire localized base*, using localization hom extensionality, and factors the original source morphism through the same open of the projective contact line. Thus the comparison does not merely put unrelated closures into isomorphic fields.

`InfinityGlobalChart318` identifies the integral closure of A in the normal source open with that in Raw, then with the explicit infinity order. The standard Mathlib theorem used here was read: it transfers an integral closure through an integrally closed ambient extension with both scalar towers, not through an arbitrary field isomorphism. The two lifts defining `IsIntegralClosure.equiv` are inverse by injectivity into the same ambient field, and `sourceClosureEquiv_embedding` retains the actual embeddings.

`NormalizationChart318` proves the affine source preimage is the whole source, constructs source/target section isomorphisms, and proves their actual map square. `IntegralClosureSquare318` maps integral elements in both directions through compatible base/ambient isomorphisms. `NormalChart318.sectionsEquiv` then uses the actual normalization section object. Composing these maps gives the section ring of the actual global infinity open, not a detached affine model. `InfinityGlobalScheme318.chartEmbedding` is Spec of this equivalence followed by the actual affine-open inclusion. Its exact range is proved.

The independent structural square is also present: `InfinityStructureMap318.chartEmbedding_over_contact_line` invokes `NormalizationBaseCompatibility318`, whose section/base square and contravariant Spec calculation were read. On the finite side, `SourceClosureComparison318` explicitly retains whole-source normality until `SourceGlobalAffine318` supplies it via four principal opens and normality descent. The finite chart has its actual range and contact-line/Q structure squares. `ContactGlobalSmooth318` uses these same two embeddings and their ranges for a genuine cover, not an asserted overlap isomorphism.

A separately packaged formula identifying the *whole contact source/infinity intersection* with a localization remains unfinished in the published source-character packet. `FullInfinityIntersection318` is about the separate Weierstrass gluing, not this contact normalization. That missing convenience endpoint does not negate the already constructed two open immersions into the same normalization, their exact ranges or the cover. It must not be reported as having been proved by the Raw-field formulas alone.

## 5. Global character maps are finite surjections, not isomorphisms

`SourceCharacterAlgebra318.toSource` lifts the literal cubic order into the entire source order using the proved integral-closure property inside Raw. Its embedding equality fixes the map; the coefficients commute with Q[t]. Finiteness follows from the source's existing finite Q[t]-module structure by restriction of scalars, not from a field-degree guess. The corresponding cubic and published affine maps are finite and surjective.

`SourceCharacterGlobal318.globalMap` uses normalization descent from the exact original-open map to the relative normalization of the cubic cover. It proves its projective-line square and its original-open square. Finiteness follows from the established finite composite to the projective line; dominance comes from the injective original cubic ring map, and finite dominance gives surjectivity. Its target is exactly `SourceCharacterGlobal318.Model i`. It is not the published projective elliptic curve by an implicit identification. The packet README explicitly retains projective comparison, categorical quotient, genus, Jacobian, full two-torsion and PEL boundaries.

`SourceTwistFieldEquiv318.source_equiv_of_published_scalings` was read as a boundary consumer. Its geometric coefficient scalings are explicit hypotheses for all four indices, not a conclusion of this packet. It uses both fourth- and sixth-power coefficient identities, nonzero cubic A/B, and actual invertible root scalings. It does not replace isomorphism by isogeny or equal j-invariants. This review neither rejects historical classical geometric proofs nor promotes this conditional formal interface to an unconditional PEL producer.

## 6. Confirmed published-prose mismatch and historical disposition

At the fixed commit, `receipts/contact-character-quotients/README.md` line 5 says:

> The omitted inertia flip fixes that field and the other three finite inertia flips negate its character root.

The actual endpoints `SourceCharacterFields318.omitted_flip_fixes` and `other_flip_negates` concern `FourRootAutomorphisms318.signEquiv`, with `flip i` the Boolean function changing only that root sign. They do not identify a decomposition group, valuation, or inertia generator. This is a scope overstatement in the packet summary. A narrow correction should say "omitted root-sign flip" and "other three root-sign flips", then explicitly retain the separate valuation-theoretic identification. No Lean source change is requested.

This qualification is **not new mathematics**: `reviews/contact-character-review/REVIEW.md` already states it explicitly, and the main progress README also retains it. Historical disposition: prior qualification found. Incorporation disposition at dea5d91: partly incorporated, since the packet README kept the broader wording. The author independently alerted this reviewer to the location; this reviewer then read the exact prose, definitions, endpoints and previous qualification. A later patch needs its own exact binding; this review does not preapprove unexamined edits.

## Protocol checklist and limits

1. **Required objects:** actual four-root source, three-root infinity carrier and literal cubic/short rings; all described and bound, not inferred from names.
2. **Constructed inputs:** units c for the general contact construction; fixed units only for published coefficients. Q coefficients and local alternative scalar structures retained.
3. **Coverage:** all i∈Fin 4 and all j∈Fin 3; all rational functions, whole orders and localized bases, not only named generators without generation/extensionality proofs.
4. **Maps and factors:** forward/inverse formulas and constants checked; actual section/base squares and contravariant Spec directions checked.
5. **Object identity:** character field is a subtype of the original Raw; fraction-field embeddings and actual normalization opens are explicit.
6. **Exceptional cases:** units exclude zero twists; distinct contact values and nonzero denominators are proved; no claim of rational lifted points above u=0 for every twist.
7. **Integral/rational scope:** whole affine Q-orders and their localizations; no controlled integral Z-reduction, polarization or metrized comparison follows.
8. **Downstream effect:** actual finite character maps accepted at their stated targets; geometric scaling inputs and projective/PEL interpretations remain separate. The inertia wording needs correction only.
9. **Evidence/version:** exact Git/source/prose hashes and independent arithmetic output frozen; existing replay/axiom receipts remain historical producer evidence, not a fresh reviewer kernel run.

No new broad external-source search, proof expansion or shared edit was undertaken. This is not a complete dependency audit of Mathlib, all imported Kummer/Galois foundations, all formal witnesses, or the whole manuscript.
