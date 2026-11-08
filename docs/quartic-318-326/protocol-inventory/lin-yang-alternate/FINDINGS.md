# Baba–Granath objection: the alternate Lin–Yang route

Date: 2026-11-08. Reviewer/author of this bounded investigation: model worker `/root/restart_hodge_gluing`; model identifier is not exposed. No shared source edit, compiler run, new proof module or full repair acceptance.

## Result

The selected Lin–Yang equation (2) is **not an independent resolution** of the Baba–Granath map-degree objection: its introduction expressly attributes that normalized discriminant-six parametrization to Baba–Granath. Its Example 29 does supply a different modular-intersection route. The constants in that route can be determined from its stated discriminant −24 intersection values alone, avoiding its last-line discriminant −19 orientation value. The exact algebra checks, but the full alternate application is **not yet independently accepted**: the same optimal CM point, the CM value calculation, the modular parametrization, and its final-publication conventions must be checked.

There are also two directly visible local inconsistencies in the selected Lin–Yang v1 Example 37. They must not be silently carried into a repair. These findings do not assert that the final published article has the same errors, that the global parametrization is false, or that Baba–Granath's separate abstract product-isomorphism statement is false.

The independent degree/injectivity objection and direct CM-order repair are assigned elsewhere. The distinct discriminant-210/literal-318 dependency-impact review is also separate. This packet supplies only the alternate-route investigation and its exact source/consumer boundaries.

## Sources actually read

- Baba–Granath, *Genus 2 Curves with Quaternionic Multiplication*, Canadian Journal of Mathematics 60(4) (2008), 734–757, DOI 10.4153/CJM-2008-033-7. The frozen objection and source receipt identify published Proposition 3.7's displayed map and Proposition 3.9's use of the CM labels. The independent group review, not this packet, owns the degree-four derivation.
- Lin–Yang, *Quaternionic loci in Siegel's modular threefold*, selected arXiv:1807.00466v1, SHA-256 `773518a4a30e4f4acac650b7f7c5f19decfb1f893431e6d04f4cfd0205919038`. Read introduction/equation (2), equations (14)–(15), Examples 28–29 and 33–37, and the statement and optimal-embedding definitions around Lemma 40/Proposition 41. Pages 20 and 25 were visually inspected. This is not a fresh review of every proof in Sections 7–8.
- The cached public Springer version-of-record page, DOI 10.1007/s00209-019-02372-z, identifies Math. Z. 295 (2020), 775–819. Its accessible Appendix B prints the D=6 row [s2,s3,s5,s6]=[j,j²,j³,j³(j+1)]. The main article is subscription content. Its convention locator is equation (14), while v1 uses (15) for the s-definitions. This public row corroborates the parametrization but does not finish a comparison of the hidden main-body normalization/proof. No access restriction was bypassed.

## What the alternate computation would prove

Example 29 chooses the Hauptmodul j6 on the actual X0^6(1)/W6 by j6(P−4)=0, j6(P−3)=∞, j6(P−24)=−16/27. Its divisor argument gives

- s3²/s2³ = c1 j6;
- s5/(s2 s3) = c2;
- s6/s2³ = c3 j6 + c4.

The same example obtains c4=1 from the actual intersection with the decomposable modular curve Y1 at P−4. It then considers the specified modular curve Y′5, whose period map is z ↦ [[3z,5z],[5z,10z]]. Its displayed parametrization, consistent with the preceding ψ/χ formulas in Example 37, is

s2=(t−12)², s3=t(t²−36t−432), s5=−2^10·3^5·t, s6=2^10·3^5(t²+12t+12).

Example 29 states that at the −24 intersection t=−6±6√−3. Equivalently t²+12t+144=0. Exact calculation in Q[t]/(t²+12t+144) gives

s3²/s2³=−16/27, s5/(s2s3)=1, s6/s2³=11/27.

Every denominator is nonzero. Substituting j6(P−24)=−16/27 and c4=1 gives c1=c2=c3=1. Thus the Example 29 constants need not be fixed by its final assertion j6(P−19)=81/64. No choice between the two conjugate values of t is necessary: all three ratios are rational and the same for both.

The resulting weighted tuple is [j6,j6²,j6³,j6³(j6+1)] in weights (2,3,5,6). Inserting the actual v1 relations (14)–(15) yields the manuscript's Igusa tuple after the one common weighted rescaling of weight-one parameter by −12:

[12(j6+1), 6(j6²+j6+1), 4(j6³−2j6²+1), j6³].

That rescaling has powers 1,2,3,5 on J2,J4,J6,J10. This is not a comparison of independently chosen numerical normalizations.

This is a **conditional connecting calculation**, not a proof that the two asserted t-values occur at the right integral optimal-CM points. Proposition 41 makes clear why that distinction matters: it discusses optimal embeddings and possible conductors, not just the quadratic field in a rational endomorphism algebra. The singular-relation intersection and the actual CM values must be validated at those objects before this computation can replace the affected Baba–Granath step. Nor does the calculation prove the positive-polarization/maximal-order identification of an arbitrary family.

## Two local inconsistencies in v1 Example 37

These were checked in the rendered page 25, not inferred from OCR.

1. The last line, introduced by “or equivalently”, prints s5=−2^10·3^5·j5². The preceding line has χ10=−j5/4, and the definition s5=2^12·3^5χ10 forces **linear** j5. Example 29 uses that linear expression. The same last line prints j2² in its s3 entry rather than j5². These are local displayed inconsistencies; the conditional check uses the preceding ψ/χ formulas and the consistent Example 29 tuple, not the inconsistent line.

2. The paragraph defines f1=(E2(z)−5E2(5z))² and f2=η(z)^6η(5z)^6, then identifies f1/f2 with η(z)^6/η(5z)^6+22+125η(5z)^6/η(z)^6. As printed, f1 has weight 4 and f2 weight 6, so their ratio has weight −2 rather than zero. Also, with q=e^(2πiz), f1 begins with 16 and f2 with q^(3/2), so their ratio begins 16q^(−3/2), whereas the asserted Hauptmodul begins q^(−1). The two expressions cannot be identical as printed. No corrected f1/f2 definition is adopted or claimed proved here.

The final published main-body version has not been read. A final-source comparison could show that one or both displays were corrected. Until then, the current preprint paragraph is not a complete independent justification of the modular parametrization used by the candidate route. These inconsistencies do not by themselves refute that parametrization; the public final appendix and Example 29 agree with it.

## Nine application obligations and remaining decisions

1. **Source hypotheses.** Required: the actual D=6 polarized quaternionic locus and modular forms in fixed conventions. Constructed in the proposed route: the source's X6 and specified Y′5 intersection. Match is conditional on the independent source/application check; equation (2)'s attribution alone does not discharge it.
2. **Constructed objects.** Required: the same optimal CM point P−24, not just CM field Q(√−6). The source claims that point in the actual intersection. This packet checks the algebra at its stated values, not the remaining optimal-embedding identity.
3. **Domain coverage.** Both t-conjugates give the same ratios. The chosen Hauptmodul is fixed by three points; the argument is not just a single-fiber equality. Divisor and intersection statements remain named premises.
4. **Comparison maps.** The actual period map to Y′5, restrictions of the same Siegel forms, and one weighted scaling are explicit. No Jacobian product isomorphism or integral Tate-lattice equality is inserted.
5. **Consumed-object identity.** The conclusion would be a function identity on the specified polarized quotient. An identity of algebraic expressions at a formal quadratic root alone is not that global moduli identity.
6. **Conventions.** s3²/s2³, not its reciprocal, is c1j6. The modular weights and the −12 weighted Igusa scaling are retained. The erroneous v1 Example 37 line is not used as if correct.
7. **Local conditions.** This candidate is complex/generic moduli work. It proves no integral model, tame special-fiber branch preservation, good-reduction assertion, or all-place metric statement.
8. **Exceptional cases.** The three ratios have nonzero denominators at both −24 values. The product-polarization boundary at j=0,∞ is handled through the source's divisor/point descriptions, not by dividing there. Those descriptions need the actual polarized-CM labels.
9. **Downstream strength.** V13 uses D=6 branch indices/values at 487–498 and 586–598, polarized conjugate equality at 608–618, and the invariant/height comparison near 987. The candidate could address the generic coordinate identification if its premises are reviewed. It does not close any of those stronger integral/height applications by itself. The D=210 five-contact route and literal 318 consequence are separately reviewed, not inferred damaged or repaired here.

## Status

Checked by exact finite calculation: the three conditional −24 ratios and constants, with all divisions checked by the attached script. No independent acceptance of this new calculation or of the full source/application repair is claimed. Optimal CM intersection, exact CM values, corrected modular-form parametrization and final-source conventions still require review. A non-author must review any proposed repair and the downstream manuscript change. The new source-display issues should travel with the findings ledger, without retroactively rewriting an earlier receipt.

Public artifacts contain this report, the finite arithmetic checker, its output and the receipt only. No third-party PDFs or page images are included.
