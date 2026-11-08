# Baba–Granath source and actual V13 application

Date: 2026-11-08. Author/reviewer: internal model worker /root/restart_contact_field. Runtime model identifier is not exposed in this worker's current context. Tools: primary-source web search, curl, pdftotext, rendered-page inspection, Python exact rational arithmetic and SymPy. No Lean replay, shared edits, or new PEL proof.

## Decision

The final published source has been obtained and compared with the cited preprint. Its relevant discriminant-6 statements and the literal V13 interface are now identified precisely. The bibliographic preprint-only limitation can be removed by a separately reviewed citation update. **Do not mark the entire application closed yet:** the new displayed-map proof objection in SOURCE-OBJECTION.md has a separate frozen receipt and awaits independent disposition. Neither that objection nor this report is a theorem-false verdict. The discriminant-210 five-contact route is a different construction, not an automatic beneficiary or casualty of a discriminant-6 conclusion.

All nine application obligations are itemized in APPLICATION.json. BINDINGS.json pins exact whole files and raw-byte consuming spans. CHECK.py/CHECKS.json establish finite arithmetic only.

## Authoritative publication and version changes

The final source is S. Baba and H. Granath, *Genus 2 Curves with Quaternionic Multiplication*, Canadian Journal of Mathematics 60(4) (2008), 734–757, DOI [10.4153/CJM-2008-033-7](https://doi.org/10.4153/CJM-2008-033-7). The publisher's 2018 online date is a platform publication date, not the print year. The typeset PDF records receipt in October 2005 and revision in April 2006.

Final PDF SHA-256: c711b2bed2aa0dd70d1bc1dd06c6d4a921c4b8735452bc143431f080a8cac12c. Both the literal V13 preprint URL and the MPI archive mirror were downloaded and give b049ce64f9b662af0e078f4faa9e5325cc7a99bf2d6ccda0a31a84719d031c32. That historical preprint is dated March 17, 2005. The PDFs are not identical.

The preprint's Proposition 10 becomes **published Proposition 3.9, p.744**, asserting equality of its arithmetic j with the square of its modular function j_m. Theorem 1 becomes Theorem 2.1; Lemma 2 becomes Lemma 3.1; Propositions 4 and 7 become 3.3 and 3.6; Theorem 11 becomes 3.10. The exact branch indices additionally require the §3.1 elliptic-order table, not Proposition 3.9 alone.

A real source correction occurs in §2.1: the preprint places twisting elements in the positive normalizer while requiring negative reduced norm. The final p.737 uses the full normalizer instead, resolving that incompatibility. The fixed discriminant-6 data, twisting rings, j identity, branch values and displayed weighted Igusa coordinates agree in the compared versions. Bounded publisher/web searches located no separate relevant erratum. This is not proof that no correction exists.

## The source's actual moduli object

Published §2.1 defines principally polarized triples (A,ρ,ι) with an embedding of the maximal order O and Rosati involution a↦μ⁻¹ bar(a) μ. Stable subrings are maximally embedded and preserved by that involution. Theorem 2.1 identifies the quotient after forgetting the O-label but keeping the principal polarization with the quotient by the twisting subgroup. This is a polarized-isomorphism classification, not an isogeny classification or a statement of descent to the field of moduli.

For §3 the source fixes exactly B=(2,−3), O=Z[i,(1+j)/2], and μ=2j+ij, with μ²=−6. The two twisting rings are Z[i] and Z[j+ij], corresponding to 2 and 3. They generate the entire four-element Atkin–Lehner group W in this discriminant. Lemma 3.1 gives V/W≅P¹ over Q, with the three distinguished orbits rational. Proposition 3.6 gives the arithmetic coordinate on the genus-2 locus P¹ minus 0 and infinity, and its inverse weighted Igusa coordinates are precisely

[12(j+1), 6(j²+j+1), 4(j³−2j²+1), j³].

These are the source's genus-2 Igusa conventions and j coordinate, not the classical elliptic j-invariant. Proposition 3.9 is the substantive arithmetic-to-analytic identification. Theorem 3.10 further identifies the actual canonical Shimura curve with the conic x²+3y²+z²=0; Corollary 3.11 describes the Atkin–Lehner quotient maps. Equation agreement alone would not replace these moduli identifications.

## Polarization normalization: explicit historical bridge, not equality of printed forms

V13 uses the inverse-μ form E(x,y)=Trd(μ⁻¹x bar(y)) on the ordered lattice basis (1,i,(1+j)/2,(i+ij)/2). CHECK.py reconstructs the exact displayed matrix and determinant 1. With i=diag(√2,−√2) and j=[[0,−√3],[√3,0]], the lower-left entry of μ is (2−√2)√3>0; Lin–Yang equation (3)/Lemma 3 is the matching positivity convention.

The published Baba–Granath display on p.736 instead gives Trd(bar(x) μ y). Cyclicity of trace and μ²=−6 show this is **6E**, with determinant 6⁴=1296 on this lattice, not the primitive principal form. This is also present in the cited preprint. V13 does not use that erroneous literal normalization: its historical geometry report already explicitly distinguishes the forms, uses Lin–Yang's inverse-μ form and Buzzard's uniqueness of the canonical principal polarization with the fixed involution. Thus this is a prior located bridge, not a newly assumed equation identity. The final-publication coverage of those adjacent inputs is owned separately and not silently supplied here. The scalar discrepancy should remain explicit when updating the citation.

## Branch indices and the precise level cover

The coarse degree-four map V→V/W has three branch orbits of index 2. It does **not** have coarse ramification indices 4,6,2. Those are the orders in the full normalizer orbifold: the order-2 and order-3 elliptic points of the norm-one group acquire an extra factor 2, while the third orbit has only factor 2. The published table on p.740 has one elliptic point each of orders 2,4,6 for the normalizer.

After passing to a torsion-free full-level component, the map to this orbifold quotient therefore has geometric indices 4,6,2 at j=0,infinity,−16/27 respectively. V13 lines 519–559 construct that full-three scheme, kill polarized stabilizers by the torsion-free 1+3M4(Z3) argument, and retain all determinant components. Its degree ≤324 and central-idele argument are extra manuscript steps, not conclusions of the connected complex-curve statement in Baba–Granath. No auxiliary level-five factor or discarded determinant component is hidden in this source comparison.

## Pullback, local exclusions and actual fiber

V13 takes six contacts 0,−15,−20,−24,−30,−60 and J(u)=−57600F(u)²/G(u)⁶. The finite exact check verifies G⁶−97200F²=H² and all relevant discriminant/resultant supports. Zeros of F,G,H have multiplicities 2,6,2 in the three branch pullbacks; tame normalization gives remaining indices 2,1,1. Leading coefficients add no prime above 13. The source itself proves no integral smoothness or tame-specialization result; those are V13's separate arguments at p>324 and depend on the integral-model sources.

For every rational u outside the six contacts, F(u)≠0 and disc(G)=−10800, so J(u) is rational, finite and nonzero. In fact J(u)<0. Its value at infinity is −57600/117649, an ordinary unbranched value. Each quadratic factor of H has nonsquare discriminant (10800 or 43200), so rational u does not hit the third special value −16/27 either. The positive special value 81/64 is likewise absent from this actual rational family. These exclusions prevent accidentally applying a generic genus-2 formula at a degeneracy; they do not remove the source's global coordinate-identification obligation.

Theorem 2.1 plus the rational weighted moduli point in V13 lines 608–618 gives geometrically isomorphic **polarized** conjugate surfaces after forgetting O. It does not give a surface over Q or eliminate a field-of-moduli obstruction. The later Hom-field construction works over its explicitly chosen splitting field and is not a conclusion of Proposition 3.9.

## New source-proof objection and its boundary

The separate immutable SOURCE-OBJECTION.md derives that the displayed homomorphism in published Proposition 3.7, p.743, from a genus-2 Jacobian to its two degree-two elliptic quotients has degree 4. The source's claim that this particular map is an isomorphism is not correct. Even its preceding curve-point injectivity assertion fails on pairs of opposite Weierstrass points. Proposition 3.8 invokes an analogous argument, and Proposition 3.9 uses both CM-point identifications.

This does not disprove an abstract product isomorphism by another map or the final coordinate theorem. The degree-four isogeny supplies the rational CM center, but a justified route from that information to the same optimal CM orders and polarized points must be exhibited if it is used to resolve the objection. Checkpoint has assigned non-author review; no repair is claimed here. The published source's numerical orientation test is a source-internal computation, not one replayed by CHECK.py.

## Explicit separation from the current discriminant-210 route

V13 lines 6868–6943 instead start with the indefinite quaternion algebra of discriminant 210, a genus-5 maximal-level Shimura curve X, and W≅(Z/2)^4. They use González–Rotger's published genus-one quotient models, not Baba–Granath's genus-2 surface family. Their five branch labels are 30,42,70,105,210, all index 2. With the normalization b210=infinity, b105=0, b70=1, the quartic cross-ratio comparison selects b42=2401 and b30=−343/32. Then t=32s produces contacts 0,32,76832,−343 plus infinity. This t is not Baba–Granath's j.

The finite determinant check confirms support {2,3,5,7} for the five primitive forms, but this arithmetic fact does not identify a constructed four-root cover, its Jacobian, or its PEL structure with X. Nor does the numerical agreement of the cubic/elliptic character quotients prove that identification. Such comparison maps retain their separate review obligations.

The current 318/326 arithmetic document's finite-exceptional-prime refinement explicitly consumes this five-contact geometry and its discriminant-210 height theorem; it records C=210^300 and the original five contacts. V13's sharper five-contact theorem at 8922–8953 explicitly reuses that construction and representations, not merely the exponent-24 inequality. No source theorem restricted to discriminants 6 and 10 supplies the discriminant-210 model or Yuan comparison. Conversely, the newly found discriminant-6 source proof objection alone does not refute the current five-contact route. This report is not an exhaustive certification of every indirect dependency in the final 318/326 proof.

## Required next dispositions

1. A reviewed citation update should name the final 2008 publication, Theorem 2.1, Lemma 3.1, §3.1, Propositions 3.6 and 3.9, and retain the separate normalization bridge.
2. Resolve the source's displayed degree-four map objection and the exact amount of CM identification needed by Proposition 3.9. Preserve the source statement versus its supplied proof distinction.
3. Keep the discriminant-210 source/Jacobian/PEL comparison and the integral-model inputs independent. This packet does not close them.

Public release files are listed in receipt.json. PDFs, rendered pages and extracted third-party text remain local evidence and must not be included in the public archive.
