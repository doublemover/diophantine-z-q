# Milne IV.7.3 family erratum: bounded nondependency finding

Decision: **no use of the corrected IV.7.3(a) coarse-family assertion was found in the inspected V13 or literal318 family producers. No repair to those producers follows merely from this erratum.** This is a dependency finding, not a fresh acceptance of their PEL, integral-model, metric or arithmetic claims.

## Source correction and attribution

Milne's *Abelian Varieties*, v2.00 (2008), printed p.154, IV Theorem7.3(a), asserts representative families near every coarse-moduli point. The official errata restricts that claim to points outside a codimension-one closed subset and credits Martin Orr's obstruction at elliptic orbifold points. Thus a generic representative family cannot automatically be extended around every coarse point. Orr is credited for challenging this source statement, not this project. The actual theorem statement and the official correction were freshly read at https://www.jmilne.org/math/CourseNotes/AV.pdf and https://www.jmilne.org/math/CourseNotes/errata.html. The original proof's uniqueness step also uses the overstrong property; this note does not certify a replacement proof of the whole coarse-moduli theorem.

Earlier direct PDF requests returned406. Official indexed text was readable; its exact tool response is retained locally. No freshly downloaded PDF byte match or new publisher-typeset comparison is asserted.

## Actual routes used by the project

1. **V13 discriminant-six family, lines519–554.** The manuscript invokes Buzzard's fine V1(5) model over Z[1/30], then adds full five- and three-markings. It proves that the group changing only the five-marking acts freely, using the remaining full three-marking, and descends the universal polarized abelian scheme to that quotient. Its later A/K is a fiber of this marked family. This is a fine-level construction and descent, not a representative family on a neighborhood of every point of a coarse Siegel variety. Historical A002 explicitly describes the same route.
2. **V13 discriminant-210 five-contact family, lines6940–6948.** The manuscript instead invokes Yuan's maximal moduli stack with its universal abelian surface and the full principal-level-three fine scheme. The universal object is on the stack/fine cover. It does not claim that the coarse contact line itself has a representative abelian family near every point. The later height evaluation uses the actual stack morphism. Whether all these named producers and their metric identifications are proved is a separate application review.
3. **Literal318 auxiliary open-j family, arithmetic.md1494–1510.** It writes an explicit elliptic equation over U=Spec Z[1/(6N),j,1/(j(j−1728))]. Thus the exceptional j-values0 and1728 are deliberately excluded. It forms primitive torsion and the H-orbit quotient, with −1 in H, to remove the choice between local isomorphisms. It never claims a universal family at the excluded coarse points. OpenJModel318.lean directly constructs this ring/model, proves unit discriminant and the j formula, and retains these statements under base change; it does not invoke Milne IV.7.3. No new compiler replay was run for this reading.

## False-positive citations and search boundary

The actual V13 citations to the AV notes are I.2.8–2.9 (complex-torus algebraicity) and I.12.1(a) (Tate duality), with the AV bibliography at21736–21738. The two visible citations to a proof of I.7.3, at4212 and12216, use the distinct bibliography key `milne`: *Arithmetic Duality Theorems*, second edition2006, ChapterI. They concern isogeny ratios and are not the AV family assertion.

The historical application inventory has six entries listing `milne-av`: A009,A011,A061,A063,A064,A079. Their source locators involve Tate duality, algebraicity, endomorphism lattices, Poincare complement and good reduction, not IV.7.3. The enumerated current sources, locators, exact searches and whole/excerpt hashes are preserved in the manifest and search record. This is bounded nondependency after tracing the actual producer arguments, not proof that an external theorem's entire transitive literature never touches coarse moduli.

No correction, new objection, or new acceptance should be added to the literal318 PEL/metric construction solely because this unrelated erratum exists. Existing integral-model/KS, source identification, height49/8 and all-row witness obligations remain exactly open or reviewed as their separate records say. Historical reviews and pins are unchanged; no shared source edits or PR were made.
