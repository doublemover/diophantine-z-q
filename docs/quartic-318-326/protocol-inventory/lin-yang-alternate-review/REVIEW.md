# Independent review of the Lin–Yang alternate-route findings

Date: 2026-11-08. Reviewer: `/root/restart_modular_curve`, not the author of the findings under review. Runtime model identifier was not exposed. No shared edits, Lean compilation or proposed manuscript repair.

## Decision

**Accept the bounded findings and conditional arithmetic in Hodge receipt `9f5ca044f025377a45c33ce9f609e8615d714d07f7092afaa6f494c1b6afdf38`, with an explicit publication-evidence qualification.** This accepts the two local inconsistencies in the selected v1 text and the −24 calculation assuming its stated CM/modular premises. It does not accept the alternate route as a completed independent proof of the D6 parametrization.

The final public Appendix B corroborates the resulting D6 tuple only. It does **not** verify the intermediate Y′5 parametrization, the f1/f2 derivation, its optimal-CM intersection or its t-values. The source author has agreed to this qualification and will preserve it separately rather than silently changing the frozen report.

## Source and independent reading

The selected preprint is arXiv:1807.00466v1, PDF SHA-256 `773518a4a30e4f4acac650b7f7c5f19decfb1f893431e6d04f4cfd0205919038`. I read the introduction/equation(2), the form/Igusa definitions(14)–(15) on p17, Examples28–29 on pp19–20, and the modular-curve setup and Examples34–37 on pp24–25. Page20 was visually inspected. Page25 was additionally freshly rendered directly from the pinned PDF and visually inspected, rather than accepting a text extraction or the author's description.

The final article is Math. Z.295(2020),775–819, DOI https://doi.org/10.1007/s00209-019-02372-z. The retained official publisher page exposes its Appendix B and labels the main article subscription content. I inspected that cached publisher text; this is not a newly retrieved final main-body PDF. Its definition locator is equation(14), whereas v1 uses(15), so numbering cannot simply be carried across versions. No claim is made that the v1 display problems persist in the final article. No access bypass or purchase was attempted.

## 1. The Example37 weighted tuple is inconsistent as printed

The preceding displayed weighted tuple has χ10=−t/4, where t=j5. Definition(15) says s5=2^12·3^5χ10, hence its s5 entry is −2^10·3^5t. Example29 uses this linear expression. The last line on p25 instead prints −2^10·3^5t². It also prints j2² in the s3 entry where the preceding line and Example29 have j5². Both are visible in the original page, not OCR artifacts.

The s5 discrepancy is not resolved by changing a weighted-projective representative. In weights(2,3,5,6), s5²/s2^5 is weight zero. Changing linear t to quadratic t, while retaining the printed s2, multiplies this invariant by t², a nonconstant function. Thus the two displayed parametrizations cannot be equivalent generically as printed. Identifying the inconsistent line does not establish a replacement global parametrization.

## 2. The printed f1/f2 cannot be the stated Hauptmodul

The paragraph defines f1=(E2(z)−5E2(5z))² and f2=η(z)^6η(5z)^6. The combination E2(z)−5E2(5z) has weight2 on Γ0(5), so f1 has weight4. The eta product has weight6 (with its multiplier). Their ratio has weight−2, not zero. In particular f1−12f2 also mixes different weights in the preceding asserted restriction formula. The source's own Section6 explains that restricting a Siegel form of weight k gives elliptic weight2k.

There is a direct cusp check independent of transformation conventions. With q=exp(2πiz), η(z)=q^(1/24)(1+O(q)) and the usual normalized E2 has constant1. Thus f1=16+O(q), f2=q^(3/2)(1+O(q)), and f1/f2 begins16q^(−3/2). But η(z)^6/η(5z)^6+22+125η(5z)^6/η(z)^6 begins q^(−1). The two expressions are unequal. A constant normalization cannot fix different q-orders. No corrected f1 or f2 is proposed or adopted by this review.

## 3. The conditional −24 arithmetic is correct

Assume the actual point/intersection and modular-function assertions of Example29, including t=−6±6√−3 at the specified optimal CM point, the displayed Y′5 tuple, the three divisor-based identities, j6(P−24)=−16/27 and c4=1. This review does not independently establish those geometric premises.

A short independent reduction makes the exact calculation transparent. Modulo t²+12t+144=0,

- t³=1728 and t≠0;
- s2=(t−12)²=−36t;
- s3=t(t²−36t−432)=6912;
- s5=−248832t;
- s6=248832(t²+12t+12)=−32845824;
- s2³=−80621568 and s2s3=−248832t, both nonzero.

Consequently the three weight-zero ratios are

s3²/s2³=−16/27, s5/(s2s3)=1, s6/s2³=11/27.

The identities s3²/s2³=c1j6, s5/(s2s3)=c2 and s6/s2³=c3j6+c4 therefore give c1=c2=c3=1. Both conjugate values of t give the same result. The −19 value and its orientation are not needed for this conditional calculation. The still-required divisor and c4 arguments are not replaced by the calculation at one quadratic root.

Using the D6 weighted tuple [j,j²,j³,j³(j+1)] and(14)–(15), the unscaled Igusa representative is

J2=−(j+1), J4=(j²+j+1)/24, J6=−(j³−2j²+1)/432, J10=−j³/248832.

A single weighted scaling by−12, with powers1,2,3,5, gives exactly

[12(j+1),6(j²+j+1),4(j³−2j²+1),j³].

The attached independent checker uses polynomial reduction and rational arithmetic, not the author's implementation. It verifies these identities and every denominator used. This is a finite algebra check, not a formalized theorem about CM points or modular forms.

## 4. Exact effect on the current manuscript

The pinned V13 SHA is `9db71bbfcefb37db56eabcf40a5f9dd85de9ed58294635da3dbf6d4f5caa8fcd`. It cites Lin–Yang at495,498 and987, all in the D6 route. At608–618 it uses the D6 Igusa tuple for the actual polarized moduli point. At984–1005 it uses the same D6 representative to derive ψ4=144j and χ10=−j³/4, hence the invariant theta ratio. The algebra from that representative is correct.

V13 does **not** insert the faulty Example37 f1/f2 expression or its quadratic-s5 line in these displayed calculations. The new local preprint issues therefore obstruct using that paragraph as an already complete alternative proof; they do not demonstrate a new direct bad substitution in V13. The underlying D6 source-identification issue remains because introduction equation(2) expressly attributes the parametrization to Baba–Granath. Merely citing that equation again is not an independent repair of the BG proof concern.

The integral branch-preservation and full height application remain stronger than the conditional complex-coordinate calculation. No optimal integral CM identification, polarized universal-family comparison, special-fiber theorem or height theorem is supplied here. The current literal318/326 construction's separate D210 route is covered by the frozen dependency-impact receipt `0c61654197ba2dddb25375bab62e0b137742040a11156e000e1ba4d89b42be07`; this review does not reopen or promote that bounded conclusion to global acceptance.

## Nine-obligation disposition

1. Source hypotheses: selected-v1 formula discrepancies verified; final main-body equivalence remains open.
2. Constructed objects: source names actual X6, Y′5 and P−24; this review does not newly identify the optimal CM object.
3. Coverage: both t-conjugates and all displayed arithmetic denominators checked; global divisor identities remain premises.
4. Maps: Y′5 period map and same-form restrictions are named prerequisites; one weighted rescaling is checked, no substitute integral map invented.
5. Consumed object: V13 uses the D6 tuple, not either erroneous Example37 display; actual moduli identification still needs its source proof.
6. Conventions: weights, q-orders, s5 normalization, ratio orientation and Igusa scaling checked explicitly.
7. Local conditions: only the complex/cusp contradiction is checked; no finite-place or integral consequence is inferred.
8. Exceptional cases: t≠0 and both denominators are nonzero; no division at j=0 or infinity is licensed.
9. Downstream use: bounded findings accepted, complete repair not accepted; final publication and actual CM/modular premises remain open.

Public artifacts exclude source PDFs, images, HTML and extracted source text. They contain this report, exact source/consumer hashes, the independent finite checker, its output and the receipt.
