# Lin–Yang: actual V13 use and the separate discriminant-210 route

Reviewer: `/root/restart_group_law`. Date: 2026-11-08. Bounded non-author internal-model review, with no manuscript change, proof expansion, compiler replay or global acceptance. The exact sources, nine comparison obligations, consumer passages and retained arguments are bound in `manifest.json`.

## Findings

1. **The proposed discriminant-210 Lin–Yang seam is not an actual dependency found in the manuscript or retained producers.** V13 cites Lin–Yang at lines 495, 498 and 987, all in the discriminant-six/six-contact argument. The discriminant-210/five-contact construction instead cites González–Rotger for the quotient models, Deligne for the canonical-model action, and Yuan for the actual integral PEL model and Kodaira–Spencer isometry. The final 318 height49/8 route retains that five-contact construction.
2. **The selected Lin–Yang v1 application at discriminant six checks.** The chosen positive involution, same polarized abelian surface, Hauptmodul normalization, weighted coordinates and nonvanishing domain agree with the source. No equation-only inference is substituted for its moduli interpretation.
3. **There is substantive prior classical identification for discriminant 210.** `FIBER-PRODUCER.md` and `MAXIMAL-KS-PRODUCER.md` contain the connecting argument and exact forget-level/universal-fiber map. The absence of a constructed Lean PEL object is not evidence that no classical argument was supplied. This review locates and reads that argument; it does not freshly accept all its external sources.
4. **Final-publication equivalence is limited.** The cited arXiv v1 bytes were freshly verified. Publication and the publisher's public Appendix B were checked, but the main journal body remains subscription content. Equation numbering changes between versions. This report does not label the selected preprint as final published text or close every selected-to-final comparison.

## Source versions and what was read

The selected source is [arXiv:1807.00466v1](https://arxiv.org/abs/1807.00466v1), submitted 2 July 2018, with a manuscript date of 3 July 2018. Fresh PDF SHA-256 is `773518a4a30e4f4acac650b7f7c5f19decfb1f893431e6d04f4cfd0205919038`, exactly the retained audit pin. The live arXiv history lists v1 only. Read the introduction and equation (2), §§2 and 5 with equation (3), Lemma 3 and its proof, definitions of the polarized quaternionic locus and stable group, equation (14), and Example 29's discriminant-six normalization. Pages 3 and 17 were also viewed as rendered pages.

The [publisher record](https://link.springer.com/article/10.1007/s00209-019-02372-z) confirms *Mathematische Zeitschrift* 295 (2020), 775–819, online publication 2 August 2019, DOI `10.1007/s00209-019-02372-z`. Its public Appendix B includes the discriminant-six parameter row and explicitly directs readers to arXiv for its longer tables. However, the publisher calls its definitions of s_k equation (14), whereas the selected v1 uses equation (15) for those definitions and equation (14) for the Igusa/modular-form relations. Locators cannot therefore be copied to the final edition by number alone. The accessible appendix is corroboration, not a complete check of the final polarization and invariant conventions. No subscription purchase or access bypass was attempted. A bounded title/correction search and the publisher/arXiv pages revealed no separate correction, not an exhaustive no-erratum guarantee.

The historical `parallel-geometry-report.md` was read in full at the relevant A001/A002 scope. It already supplies the lattice/polarization comparison and warns that equations (2), (14) are not the Riemann-form locator: the actual latter locator is equation (3) and Lemma 3. V13 incorporates that corrected application-site locator. Older whole-height and current Hodge-inventory arguments were also read, not merely their conclusions.

## Actual discriminant-six application

The source's quaternionic locus Q_D consists of principally polarized abelian surfaces carrying the specified maximal-order action **with the specified positive Rosati involution**. It is not the set of every principal polarization on an arbitrary QM surface. Nor does an arbitrary curve with matching numerical invariants automatically supply the required chosen integral family.

V13 takes B=(2,−3), O=Z[i,(1+j)/2], μ=2j+ij, and the form Trd(μ⁻¹x conjugate(y)). This is exactly the convention of source equation (3). The stated lattice matrix is integral and unimodular. For i=diag(√2,−√2) and j=[[0,−√3],[√3,0]], the lower-left entry of μ is (2−√2)√3>0, meeting Lemma 3's positivity criterion. The Rosati formula μ⁻¹ conjugate(a)μ is the defining one. The retained maximal-order/discriminant identification and prior exact matrix calculation remain named predecessors; they are not inferred merely from a theta equation.

Source equation (2), printed page 3, is explicitly the map from X₀⁶(1)/W₆ to Q₆, with j taking values 0, infinity and −16/27 at CM discriminants −4, −3 and −24. It gives the weighted Igusa coordinates used by V13. The actual abelian surface is the same polarized universal fiber from the full-three construction, after forgetting the level/order labels as prescribed. The argument first identifies that moduli datum; only then does it substitute its coordinates.

At the height-comparison site, j=J(u)=−57600F(u)²/G(u)⁶ is finite and nonzero for the allowed rational u: F(u) is nonzero by contact exclusion, while G has negative discriminant and no rational root. Thus the exceptional product-polarization locus at J₁₀=0 is not used, and division by ψ₄ is legitimate. CM points on this allowed locus are not silently excluded.

Using one common weighted representative, the source relations give

- J₂=12(j+1), J₄=6(j²+j+1), J₁₀=j³;
- ψ₄=J₂²−24J₄=144j and χ₁₀=−J₁₀/4=−j³/4;
- j=16·144⁵·χ₁₀²/ψ₄⁵.

The two terms in the ratio have the same modular weight, so this identity survives the weighted scaling. It is an equality of functions on the specified polarized moduli curve, not an equality of differently normalized coordinates on unrelated models. The later theta expressions come from the separately cited Lauter–Naehrig–Yang input, and the theta-height bound from Pazuki; their final-source applications are not newly reviewed here. Lin–Yang supplies neither an integral model at bad primes nor the entire height inequality.

The source explains the generic map X₀ᴰ(1)/W_μ to its polarized image and allows different components/self-intersections in general. The reviewed D=6 equation has its explicit identification. It must not be silently promoted to a D=210 full-Atkin–Lehner quotient or a statement for every component/polarization.

## What actually identifies the five-contact object

The manuscript's five-contact proof starts with the actual discriminant-210 Shimura curve X, not a curve reconstructed solely from four j-invariants. V13 lines 6868–6938, and the retained `FIBER-PRODUCER.md` §§1–2, use González–Rotger's identification of the four quotients X/⟨w_m⟩, m=30,42,70,105. Genus five, the W=(Z/2)^4 action, Riemann–Hurwitz, tangent faithfulness and the inertia-product relation identify the five rational branch labels. This is the essential geometric antecedent to the coordinate calculation.

On each actual genus-one quotient, the residual exponent-two order-eight group has translation subgroup equal to the full two-torsion. Quotienting by those translations has the same j-invariant through multiplication by two. Hence the quartic j-invariants constrain the four **actual branch subsets**. The exact cross-ratio calculation then fixes (λ,μ)=(2401,−343/32), with labels 210,105,70 normalized to infinity,0,1. Scaling t=32s gives contacts infinity,0,32,76832,−343. This prior argument explicitly avoids inferring the desired geometric source solely from agreement of equations.

The fiber producer then uses the whole canonical level-three model, its normalizer action and its constant regular fiber to obtain the controlled field and actual abelian surfaces. Its §§3 and 7 identify the PEL datum with Yuan's maximal-order model, not with a Lin–Yang table. The separate `MAXIMAL-KS-PRODUCER.md` further supplies the exact map

(A,i,η) on the fine level-three model → (A,i) on the maximal stack.

The surface A is literally unchanged. Pullback of the universal surface identifies its Hodge determinant with det H⁰(A,Ω¹_A), compatibly with the specified O-action and polarization. The bicanonical sections are pulled back from the maximal stack, not reinterpreted as the dualizing bundle of a ramified level cover. This explains why the integral image factor is 210 and why neither the 36 marking count nor the 576 fiber count is an extra point-height factor.

These project-authored notes are internal mathematical connecting arguments, not an unpublished external theorem silently assumed because a bibliography item exists. They explicitly invoke the named PEL/canonical/stable-model results. Their merits and independent review are separately recorded in the contact-metric and five-contact assembly reviews. This pass has read their actual content and located it; it has not independently re-proved González–Rotger, Yuan, Deligne or the whole height-transfer chain.

## Exact current consumer and remaining boundary

The contribution's `RefinedContactRealization318.MetricSections` requires actual frame norms, `hodge_degree`, the placewise `ks_image`, finite integrality and archimedean bounds. Its exact parameter ratio is 32u/v. `RefinedGeometricRealization` quantifies every primitive noncontact rational point and retains both CM and non-CM branches. `RefinedSoundness318326.source_soundness`, `polynomial318_soundness` and `stored326_soundness` still take that proposition as a hypothesis.

The later explicit Kummer/contact normalization and character-field/affine Weierstrass packets are valuable constructions. Their own reviewed endpoints exclude the final geometric quotient/PEL identification. In particular, matching their specified twists and affine fraction fields to published genus-one models is not yet a construction of the universal abelian surface or of the integral Hodge/metric data demanded by the consumer. That is a real formal producer boundary, not a missing Lin–Yang theorem and not a refutation of the prior classical notes.

Historical disposition: the relevant discriminant-six justification and the distinct discriminant-210 classical connecting argument were found and read. Current incorporation: those arguments are present in V13 and the retained project producers. Remaining work includes exact final-publication comparison for the selected Lin–Yang locators, the separately scoped source-to-object reviews for González–Rotger/Yuan/Deligne, and the actual formal realization/global arithmetic assembly. No unconditional 318/326 conclusion follows from this report.
