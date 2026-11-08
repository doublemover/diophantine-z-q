# Hodge, Arakelov and isogeny application inventory

Bound revision: `09e35ad61946e92561460d93c3e57831ea5e3117`.

**Decision: incomplete review, not rejection.** No new proof expansion or compilation was performed. This report does not approve a full proof or remove `RefinedGeometricRealization`.

## Immediate findings

1. The literal refined 318/326 soundness endpoints explicitly assume `RefinedGeometricRealization`. Its placewise KS image identity, actual integral section data and actual Arakelov/isogeny data remain producer obligations. The conditional inequalities are proved; their actual geometric instantiation is a separate task.
2. Fresh inspection of the published MSP Javanpeykar PDF confirms the minimal-model inequality direction, non-Weierstrass hypothesis, positive normalization shift and the residue-prime range in the local different bound. This improves the earlier arXiv-v1-only source check, without accepting the whole geometric application.
3. Yuan is a published theorem. The author explicitly identifies the April30,2024 English PDF as a translation of the published Chinese article. Its integral image statement and metric isometry are stronger data than a rational line isomorphism. The current downloaded bytes match the historical metric review.
4. The current Gaudron–Rémond author PDF also exactly matches the older source hash. The published work exists, but this pass did not obtain its final theorem pages. Rémond’s June2021 author version is readable; the publisher’s final PDF requires a subscription. Both final-text comparisons remain open.
5. V11 and the contribution use different non-CM height routes: V11 has generic Belyi bounds and an isogeny with source J_H; the contribution uses direct finite-divisor domination, Wronskian cancellation and a dimension-two image. The latter must have its own application record and cannot inherit acceptance merely from V11.
6. Existing classical producer notes are substantive mathematical evidence. Unconstructed Lean data alone do not establish an invalid classical application. Existing qualifications and incomplete review must not be relabeled as new errors.

## What our frozen geometry does and does not supply

The actual Weierstrass family has a proved global relative differential frame and canonical Hodge evaluation isomorphism over a domain base with unit discriminant. The actual contact normalization has five intrinsic local differential frames. The frozen tensor foundation constructs genuine tensor-square sheaves and local regular section candidates. None of these results identifies the contact normalization with the maximal discriminant210 PEL stack, constructs its universal abelian surface, identifies the canonical determinant KS morphism, proves the induced integral lattice equality at bad primes, or identifies the Petersson/Faltings metrics. The local tensor candidates have not yet been globally glued or identified with the rational q0,q1 formulas.

## Exact consumers and next missing joins

- `MetricSections.ks_image`, `hodge_degree`, `finite_integral`, `arch_bound`: bind the actual maximal-stack PEL fiber, integral canonical square, Hodge determinant, metrics and sections. Keep the maximal-stack pullback distinct from the level-cover dualizing line.
- `ArakelovIdentifications.minimal_model`, `faltings_wronskian`, `GR_normalization`: use the same actual modular curve, selected non-Weierstrass point, model, differential coordinates and cotangent metric.
- `FiniteData`: identify its real matrices and section weights with actual exceptional intersections and local different coefficients, and supply the precise vertical support/projection formula.
- `NonCMInputs.image_bound`, `isogeny_variation`: construct the same-field dimension-two image and isogeny, keep the controlled degree separate from auxiliary averaging fields, and close final-source version checks.
- `CMInputs`: bind actual periods, fundamental discriminant support, Silverman formula, product height and same-field isogeny. The 854R bound is a surface-height bound, not directly a contact-height bound.

## Source status

### yuan2024
- Acta Mathematica Sinica, Chinese Series 67(2) (2024), 227–249; DOI10.12386/A20220154
- Selected version: April 30, 2024 English translation; author explicitly identifies it as a translation of the published Chinese article.
- [Source](https://faculty.bicmr.pku.edu.cn/~yxy/preprints/explicit_KS.pdf); SHA256 `ad751f65ac5730b437adbabba78cc6bc1fe1f2249367c74566fe0a495100740e`.
- Read scope: Definitions pp2–3; Theorem1.1 p3; distinction from coarse/level models; author publication attestation. No independent comparison with Chinese text.
- Correction check: Author page and targeted search checked; no correction to this article located. An erratum link on the author page belongs to the different Gross–Zagier book.

### javan2014
- Algebra & Number Theory 8(1) (2014),89–140; DOI10.2140/ant.2014.8.89
- Selected version: Publisher PDF.
- [Source](https://msp.org/ant/2014/8-1/ant-v8-n1-p04-s.pdf); SHA256 `ec890fb41c58dee038ee2e06b530954f3aab85035238cd54a4c0ef081fcb8ea0`.
- Read scope: Definitions around sections2.2–2.3, Lemma2.3.1 pp98–99, Theorem2.4.1 pp99–100, Lemma2.4.4 p101, Lemma4.2.3 p116; prior review read for the wider composition. Not a full-paper correctness audit.
- Correction check: Author publication list and targeted title/erratum search checked; no article-specific correction located. Other author errata were not attributed to this paper.

### remond2022
- Annali Scuola Normale Superiore Pisa23(3)(2022),1589–1596; DOI10.2422/2036-2145.202010_062
- Selected version: June2021 author PDF.
- [Source](https://www-fourier.univ-grenoble-alpes.fr/~remond/2476.pdf); SHA256 `e23a019a7432e299014ead57a1ba51c3945b8351a64c96f339536786c8f79c5d`.
- Read scope: Corollary1.2, normalization note and stable-height observation pp1–2.
- Correction check: Author page, journal page and targeted title/correction search checked; no source-specific correction located.
- Limit: Journal confirms publication; article PDF requires subscription and redirects to subscription page. No paid access attempted. Final-text comparison remains open.

### gr2023
- Mémoires SMF176(2023),vi+123pp; DOI10.24033/msmf.484
- Selected version: September2022 author PDF; exact same SHA as old Javan review’s isogeny source.
- [Source](https://lmbp.uca.fr/~gaudron/art20.pdf); SHA256 `4ac73d953938fb6ceb5b2359fdfa7de85456d15b9a03d26e4237faede14b05d8`.
- Read scope: Section1.5, original height convention and Theorem1.9(1), author PDF printed pp14–15. Publisher excerpt only contains front matter; V11 published locator pp7–8 has not been compared.
- Correction check: Author publication list, publisher page and targeted title/erratum search checked; no source-specific correction located.
- Limit: Publisher publicly exposes only sample front matter in the inspected page. Final theorem text not obtained in this pass; no purchase attempted.

### cm2017
- Research in Number Theory3(2017),article13; DOI10.1007/s40993-017-0077-7
- Selected version: Publisher open-access article and PDF.
- [Source](https://link.springer.com/article/10.1007/s40993-017-0077-7); SHA256 `8752beb7b997e31a1f8a5e3ec5a13f5d8c0b675f7862305f1a873cd4b9f5ec8d`.
- Read scope: Original-normalization definition and equation6.2 in section6, including the subsequent distinct class-average step. Silverman1986 Proposition1.1 is cited there; its original chapter was not freshly inspected.
- Correction check: Article page inspected; no dedicated comprehensive correction search completed.

## Nine-obligation records

Each row below separates required input, available construction/proof, and remaining match. The evidence IDs resolve to whole-file and exact-passage hashes in `evidence.json`. No row set is a final acceptance.

### HODGE-YUAN-210
Produce MetricSections for the actual discriminant-210 PEL surface at every admissible rational contact point.

**Source hypotheses**
- Required: Indefinite quaternion algebra, maximal order, determinant condition, the stated principal polarization, actual universal abelian surface and level U.
- Available: V11 names these objects and uses maximal U (n(U)=1) for the integral comparison.
- Match/remaining: The translation theorem has exactly this moduli setting; same-object identification of the constructed contact normalization with that stack is not supplied by the elliptic Hodge packet.
- Evidence: v11-model, v11-yuan-version, elliptic-hodge. Status: incomplete_review.

**Constructed objects**
- Required: Actual maximal regular semistable stack, its dualizing square, Hodge determinant and evaluated integral sections.
- Available: Actual relative Ω and five local frames on the contact normalization; separate actual Weierstrass Hodge evaluation isomorphism.
- Match/remaining: These are useful geometric constructions but neither is a construction of the PEL surface/Hodge determinant, and the new tensor packet has only local sections.
- Evidence: contact-frames, elliptic-hodge, metric-fields. Status: incomplete_review.

**Domain and index coverage**
- Required: All primitive u,v with all five contact forms nonzero, all number-field places and all needed components.
- Available: RefinedGeometricRealization quantifies this exact domain; MetricSections quantifies every infinite and finite place.
- Match/remaining: A constructor satisfying those quantified fields for the actual PEL fibers remains absent. No argument may replace all places by generic-fiber data.
- Evidence: realization, metric-fields. Status: incomplete_review.

**Transition and comparison maps**
- Required: The canonical determinant KS map, correct pullback from maximal level, and induced integral image lattice.
- Available: InducedLattice318 derives degree from an equality of actual placewise frame norms.
- Match/remaining: Need identify the map and lattices before using the scalar conclusion; an abstract/rational line isomorphism cannot supply ks_image.
- Evidence: image-degree, metric-fields, v11-metric. Status: incomplete_review.

**Identity of consumed object**
- Required: The contact curve and bicanonical sections must be those pulled back from the same maximal stack whose abelian fiber has the stated height.
- Available: The scalar consumer accepts two coordinates and two FrameNorms records.
- Match/remaining: Those records do not themselves encode a scheme or a universal abelian surface. An external construction-to-record interpretation is required.
- Evidence: contact-consumer, metric-fields, prior-assembly-review. Status: incomplete_review.

**Coefficient and normalization conventions**
- Required: Petersson norm 2 Im τ; surface Hodge squared norm (2π)^−2 integral; image 210·ω² with induced metric.
- Available: The freshly checked translation and the old packet agree. Lean induced_degree gives −log210 for the sublattice, hence +log210 for ambient canonical degree.
- Match/remaining: The sign/metric convention checks pass at statement/conditional-algebra level; actual Hodge degree must still equal the designated surface height.
- Evidence: image-degree, metric-fields, prior-normalization. Status: bounded_statement_match.

**Local conditions**
- Required: Integral extension at every finite place, including 2,3,5,7, and the archimedean norm estimate for the same sections.
- Available: The metric producer derives estimates conditionally on the regular semistable model; MetricSections retains finite_integral and arch_bound.
- Match/remaining: Rational Ω frames over Q do not discharge bad-prime integral extension. J²q_i and their valuations need the actual integral model.
- Evidence: prior-metric-producer, metric-fields. Status: incomplete_review.

**Exceptional cases**
- Required: Finite branch points, infinity, vertical zeros, level-stack stabilizers and no hidden ramification-line correction.
- Available: Classical notes use q0 vanishing to order two at infinity and q1 nonvanishing; allow common vertical zeros.
- Match/remaining: These cases are recorded; whole-intersection identification and gluing of new tensor local sections remain separate unfinished proof work.
- Evidence: v11-metric, prior-metric-producer, prior-assembly-review. Status: incomplete_review.

**Downstream consumption**
- Required: Produce MetricSections, then its original/shifted bound, then the literal soundness consumers.
- Available: Exact conditional chain is present and uses t=32u/v.
- Match/remaining: No theorem in this lane removes RefinedGeometricRealization. Completion of the source application and a term of that proposition are distinct from its conditional numerical consequences.
- Evidence: metric-fields, realization, literal-consumer. Status: incomplete_review.

### ARAK-JAVAN-CANCELLATION
Instantiate the actual cusp/Jacobian Arakelov identities for the contribution’s quadratic-log bound.

**Source hypotheses**
- Required: Smooth projective geometrically connected curve, positive genus, chosen non-Weierstrass point and regular arithmetic model.
- Available: Contribution names the Q-defined modular cover X_H with g≥2 and a selected reciprocal fiber.
- Match/remaining: Published theorem hypotheses match that intended setting; the actual cover, selected point and model must be bound to the producer data.
- Evidence: contribution-height, actual-cusp. Status: incomplete_review.

**Constructed objects**
- Required: Global orthonormal differentials, their local coefficients, Wronskian, actual regular model and section.
- Available: ActualGlobalCusp constructs the genuine q·j function and derives energy from supplied measures/chart density.
- Match/remaining: It does not construct the global orthonormal basis or geometric chart-density identity; these remain fields.
- Evidence: actual-cusp, cusp. Status: incomplete_review.

**Domain and index coverage**
- Required: Every complex embedding of the same field and a whole selected fiber avoiding Weierstrass points.
- Available: Data.nonWeierstrass is required for each embedding; embeddingAverage uses [K:Q].
- Match/remaining: The actual geometric selection/count argument must instantiate these fields, not merely pick one complex point.
- Evidence: cusp, contribution-height. Status: incomplete_review.

**Transition and comparison maps**
- Required: Use the same cotangent metric and same local coordinate in dπ and Wronskian identities.
- Available: ArakelovIdentifications uses one metricLog in both inequalities with coefficient g(g+1)/2.
- Match/remaining: Exact scalar cancellation is checked. The map from the actual Arakelov forms to those logs remains geometric.
- Evidence: arakelov-fields, arakelov-consumer. Status: incomplete_review.

**Identity of consumed object**
- Required: hFal must be the height of Jac(X_H) for the same X_H yielding cusp data and finite intersection.
- Available: The record shares D and F parameters but hFal, pointHeight and hGR are real fields.
- Match/remaining: A record alone does not identify them with an actual Jacobian and point. Bind the source interpretation before treating jacobian_quadratic as geometric.
- Evidence: arakelov-fields, prior-javan-review. Status: incomplete_review.

**Coefficient and normalization conventions**
- Required: Minimal-model ≤ sign, factorial-normalized Wronskian, all-embedding averaging and positive g log√π shift.
- Available: Fresh published PDF checks of Lemma2.3.1, Theorem2.4.1, Lemma2.4.4 agree with the existing code and prior review.
- Match/remaining: No sign or shift discrepancy found in this bounded check. No additional half is inserted for complex pairs.
- Evidence: arakelov-fields, cusp, prior-javan-review. Status: bounded_statement_match.

**Local conditions**
- Required: Actual embedded-disc ordinary L² energy, nonzero differential and legitimate logarithmic norms.
- Available: Analytic estimates are proved from holomorphic coefficient data and actual global measure conditions.
- Match/remaining: Need identify these with global L²-normalized forms; Lean log0 convention cannot replace required geometric nonvanishing.
- Evidence: actual-cusp, cusp. Status: incomplete_review.

**Exceptional cases**
- Required: g≥2, non-Weierstrass fiber, all conjugates; auxiliary model field need not have bounded degree.
- Available: Consumer assumptions explicitly contain genus bound, candidate bound, and unrestricted averaging K.
- Match/remaining: Keep K separate from controlled isogeny field and section field. Geometric selection remains open here.
- Evidence: noncm-fields, contribution-height. Status: incomplete_review.

**Downstream consumption**
- Required: Quadratic-log Jacobian bound feeds 49/8, image/isogeny transfer and contact soundness.
- Available: SourceNonCMHeight318 derives 2^11 d²log(6dN)² and 49/8 from the named data.
- Match/remaining: This stronger cancellation route is in contribution docs, not the V11 generic Belyi R^19 argument.
- Evidence: arakelov-consumer, v11-exponent19, contribution-height, literal-consumer. Status: incomplete_review.

### FINITE-JAVAN-DIFFERENT
Instantiate the direct finite-divisor bound without an erroneous covering-degree loss.

**Source hypotheses**
- Required: Finite cover and its normal model/minimal resolution; local different estimate for residue prime p≤degree.
- Available: Published Lemma4.2.3 explicitly has 0<p≤degπ; contribution separately cites support/model lemmas.
- Match/remaining: Do not apply the lemma without that range; a separate no-branch argument at p>d is needed.
- Evidence: contribution-finite, prior-javan-review. Status: incomplete_review.

**Constructed objects**
- Required: Actual exceptional curves, intersection matrix, local canonical/pullback coefficients, and section.
- Available: FiniteData is an explicit finite real matrix/vector record.
- Match/remaining: No constructor from the actual regular model is present in the consuming module.
- Evidence: finite-fields. Status: incomplete_review.

**Domain and index coverage**
- Required: All vertical components and all required primes, including primes outside 6N.
- Available: The final sum is exactly over primeFactors(6*N).
- Match/remaining: Need prove omitted primes contribute zero on the same base-changed normalization; finite summation itself is not that proof.
- Evidence: finite-fields, contribution-vertical. Status: incomplete_review.

**Transition and comparison maps**
- Required: Canonical divisor div(dπ), pullback of the base bound and degree-one section projection formula.
- Available: The matrix negativity lemma derives effectivity from local_domination and adjunction; pullback_section is supplied.
- Match/remaining: This avoids demanding a Cartier different on the singular normalization, but still needs actual geometric coefficients and projection formula.
- Evidence: finite-fields, contribution-finite. Status: incomplete_review.

**Identity of consumed object**
- Required: The intersection consumed by minimal_model must be that of the same actual section and canonical divisor.
- Available: F.intersection is the displayed sum of coefficients times section weights.
- Match/remaining: No arbitrary replacement by a numerically similar matrix is justified; equality with actual intersection remains required.
- Evidence: finite-fields, arakelov-fields. Status: incomplete_review.

**Coefficient and normalization conventions**
- Required: Ramification multiplicities and normalized div(p) intersection log p, with no extra d.
- Available: Fresh published Lemma4.2.3 agrees with r≤2e m_p e_p.
- Match/remaining: Existing code derives the scalar bound from the exact pullback_section premise; interpretation still needs audit.
- Evidence: finite-fields, prior-javan-review. Status: bounded_statement_match.

**Local conditions**
- Required: Vertical branch support p|6N persists after the auxiliary field extension.
- Available: Contribution gives an open-j-line finite étale torsion quotient argument.
- Match/remaining: Actual global torsion quotient/coarse-model identification is an upstream construction, not supplied by elliptic Hodge triviality.
- Evidence: contribution-vertical, elliptic-hodge. Status: incomplete_review.

**Exceptional cases**
- Required: p>d, exceptional components and n=2^128+i≥2, with section not contained in support.
- Available: Finite consumer uses n≥2; nonnegative section weights and negative definiteness are explicit fields.
- Match/remaining: Positive reciprocal horizontal 3h bound is not a bound for arbitrary rational points.
- Evidence: finite-fields, contribution-finite. Status: incomplete_review.

**Downstream consumption**
- Required: Feed the same F into ArakelovIdentifications and the improved 49/8 route.
- Available: Formal data linkage uses the same F parameter.
- Match/remaining: Actual geometric identity remains an application obligation; the component matrix proof is not a full model theorem.
- Evidence: arakelov-fields, arakelov-consumer. Status: incomplete_review.

### IMAGE-ISOGENY-2
Transfer height from the actual Jacobian to its dimension-two image and then to the source surface.

**Source hypotheses**
- Required: Actual abelian subvariety C_A⊂J_H and an isogeny with A over the controlled number field.
- Available: Classical producer uses nonzero Hom and absolute simplicity to give dim C_A=2.
- Match/remaining: Neither the numerical module nor the contact-curve maps constructs this abelian image/Hom.
- Evidence: contribution-height, prior-assembly-review. Status: incomplete_review.

**Constructed objects**
- Required: A,C_A,J_H, quotient J_H/C_A and their stable heights over one compatible base.
- Available: NonCMInputs retains imageHeight and image_bound as real fields.
- Match/remaining: Need construct and identify the actual objects; arbitrary dimension-two varieties do not suffice.
- Evidence: noncm-fields. Status: incomplete_review.

**Domain and index coverage**
- Required: GR base field degree is at most 2304R; both varieties defined there, and source dimension exactly two.
- Available: Code uses a separate isogenyFieldDegree and the dimension-two logarithmic expression.
- Match/remaining: The unrestricted averaging/model field K must not be substituted into the degree bound.
- Evidence: noncm-fields, isogeny-consumer. Status: incomplete_review.

**Transition and comparison maps**
- Required: Image inclusion/quotient plus actual isogeny; apply GR with source C_A then half-log variation.
- Available: Conditional scalar bridge expands Xi² and monotonicity of the maximum.
- Match/remaining: V11 used source J_H and dimension g; the contribution deliberately changes this application and needs its own acceptance.
- Evidence: v11-exponent19, contribution-height, isogeny-consumer. Status: incomplete_review.

**Identity of consumed object**
- Required: hImage must be shifted stable height of this C_A and hSurface that of the original PEL A.
- Available: Only numerical fields and inequalities are present in the record.
- Match/remaining: Same object and normalization are obligations, not consequences of matching numbers.
- Evidence: noncm-fields, metric-fields. Status: incomplete_review.

**Coefficient and normalization conventions**
- Required: Rémond superadditivity is invariant under dimension-linear shifts; GR uses original height; variation is unchanged for equal dimensions.
- Available: Fresh author PDFs confirm these statements; algebraic monotonicity bridge is present.
- Match/remaining: Published final text comparison remains uncompleted for Rémond/GR. Both works are published, but that does not prove selected author bytes equal final statements.
- Evidence: prior-normalization, isogeny-consumer. Status: incomplete_review.

**Local conditions**
- Required: Field of definition, stable reduction for height evaluation, and absence of unaccounted degree multipliers.
- Available: Producer notes distinguish sign-lift field, section field, coefficient field and averaging extension.
- Match/remaining: Actual Hom descent and field bound must be checked in the representation lane.
- Evidence: prior-assembly-review, noncm-fields. Status: incomplete_review.

**Exceptional cases**
- Required: Use general GR Xi² case, not the stronger MM alternative; no unrequested polarization-degree hypothesis.
- Available: Fresh September2022 Theorem1.9(1) has both directions with Xi² generally.
- Match/remaining: The current dimension-two expression matches the general case, without assuming CM implies MM.
- Evidence: isogeny-consumer, prior-cm-producer. Status: bounded_statement_match.

**Downstream consumption**
- Required: Supply image_bound/isogeny_variation, then surface/contact estimate and literal soundness.
- Available: Exact numerical consumers are present.
- Match/remaining: No unconditional source or polynomial theorem follows before actual realization and source-version/application review.
- Evidence: noncm-fields, arakelov-consumer, literal-consumer. Status: incomplete_review.

### CM-PERIOD-HEIGHT
Supply the actual CM branch period, product and isogeny data for the original-normalized surface bound.

**Source hypotheses**
- Required: CM quaternionic surface with all geometric endomorphisms defined over L, [L:Q]≤576.
- Available: Classical notes derive a same-field CM elliptic factor and maximal-order quotient.
- Match/remaining: Actual abelian varieties and same-field maps are not constructed by CMProducer318.
- Evidence: v11-cm, prior-cm-producer. Status: incomplete_review.

**Constructed objects**
- Required: Actual E′, product E′², imaginary quadratic field and reduced periods at every embedding.
- Available: CMInputs lists discriminant, periods and height scalars; analytic eta estimates and numerical discriminant bound are proved.
- Match/remaining: Need identify listed periods and scalars with the actual elliptic variety.
- Evidence: cm-fields, cm-consumer. Status: incomplete_review.

**Domain and index coverage**
- Required: All embeddings for stable height evaluation, independently of original bounded isogeny field.
- Available: Separate averagingDegree and fieldDegree are explicit.
- Match/remaining: An auxiliary good-reduction extension may be large; its degree cannot replace the ≤576 parameter.
- Evidence: cm-fields, prior-cm-producer. Status: incomplete_review.

**Transition and comparison maps**
- Required: Silverman embedding-average formula, vanishing finite term after good reduction, product additivity, actual isogeny.
- Available: Published 2017 equation6.2 is the all-embedding formula; consumer retains silverman, product and variation.
- Match/remaining: Do not substitute the later CM class-average theorem requiring coefficients over Q(j).
- Evidence: cm-fields, prior-cm-producer. Status: incomplete_review.

**Identity of consumed object**
- Required: D is the fundamental discriminant of the same CM field contained in L; actual A′ is the source of the isogeny to A.
- Available: Fundamental and prime-support premises are explicit in CMInputs.
- Match/remaining: Discriminant-tower and tangent-field arguments must bind these fields to the actual surface.
- Evidence: cm-fields, prior-cm-producer. Status: incomplete_review.

**Coefficient and normalization conventions**
- Required: Original Silverman normalization, Delta=(2π)^12 eta^24, factor2 for product surface height.
- Available: Fresh publisher equation6.2 and normalization paragraph agree with retained CM note.
- Match/remaining: The output 854R is a surface bound; the contact comparison adds factor2 and +120.
- Evidence: cm-consumer, metric-fields, prior-cm-producer. Status: bounded_statement_match.

**Local conditions**
- Required: Potentially good reduction and finite discriminant support in R.
- Available: The analytic/numerical theorem assumes support and the stable formula.
- Match/remaining: Actual reduction and discriminant support are upstream geometric obligations.
- Evidence: cm-fields, v11-model. Status: incomplete_review.

**Exceptional cases**
- Required: All relevant quadratic discriminants, no exceptional-field exclusion, general Xi² rather than MM shortcut.
- Available: Fundamental-discriminant bound includes the 2-adic factor4; source uses general isogeny case.
- Match/remaining: Fresh source reading found no mismatch in those stated bounds; actual branch dichotomy still needs full application review.
- Evidence: cm-consumer, prior-cm-producer. Status: incomplete_review.

**Downstream consumption**
- Required: Original surface bound followed by MetricSections at hSurface+logπ.
- Available: CMInputs.toLegacy derives contact_metric from actual section fields.
- Match/remaining: The obsolete helper that assumes contact height≤854R is not the route used by the refined branch.
- Evidence: cm-fields, metric-fields, realization, literal-consumer. Status: incomplete_review.

## Auxiliary publication inventory and referrals

These are use-site/source-version leads, not accepted theorem applications.

- **baba-granath**: V11 six-contact discriminant6 branch/Rosati model, lines480–491; not automatically the discriminant210 five-contact model. Selected: 2005 preprint §§2.1,3,Proposition10. CJM60(4)(2008),734–757, DOI10.4153/CJM-2008-033-7 publication verified; selected-to-final statement comparison not done [Primary source](https://www.cambridge.org/core/journals/canadian-journal-of-mathematics/article/genus-2-curves-with-quaternionic-multiplication/E6B7F5233E98E9C8E013658575FF713F).
- **buzzard**: V11 six-contact fine model V1(5) over Z[1/30], lines513ff. Selected: OriginalMay13,1996; author PDF explicitly says typos fixedJune14,2002; Thm2.1,Cor2.3. Duke MathJ87(3)(1997),591–612 publication and corrected-version label verified; precise final/correction comparison not done [Primary source](https://www.ma.ic.ac.uk/~buzzard/maths/research/papers/index.html).
- **lin-yang**: V11 discriminant6 polarization and parameter equations, lines488–491 and980ff. Selected: arXiv1807.00466v1, equations2,3,14 andLemma3 as cited at actual use sites. MathZ295(2020),775–819, DOI10.1007/s00209-019-02372-z publication verified; publisher text subscription-limited, exact equation transfer not checked [Primary source](https://link.springer.com/article/10.1007/s00209-019-02372-z).
- **milne-av**: V11 complex-torus algebraicity lines633ff; Tate module/étale-H1 duality lines16494ff. Selected: Course notes version2.00,2008, PartI Theorems2.8–2.9 and12.1(a). A distinct published1986 Arithmetic Geometry chapter exists; author supplies a corrected reconstruction with unchanged chapter numbering. Do not relabel2008 notes as published. Map the exact statements to published chapter/textbook, or supply project proof; not completed here. [Primary source](https://www.jmilne.org/math/xnotes/AVs.html).
- **brinon-conrad**: V11 p-adic Hodge closure and finite-extension descent lines16501–16520. Selected: PreliminaryJune24,2009 notes.  Representation-lane referral; no publication equivalence or source-application acceptance in this review. [Primary source](https://math.stanford.edu/~conrad/papers/notes.pdf).

## Review boundary and priority

1. Reconcile this inventory with the geometric/Kato, prime-pattern and downstream-witness lanes before choosing further proofs.
2. Freeze the intended actual-object route and assign independent source-to-construction/application review. Do not substitute further local algebra for the missing PEL or Arakelov identification without showing it discharges a listed consumer.
3. Obtain/compare final published GR and Rémond text through an authorized source, or retain the precise access/version limitation. Map selected preliminary/author-version sources to published statements or supply project proofs where required by protocol.
4. Perform affected consuming-join and final closure review after incorporation. This report is not that closure.

Reviewer disclosure: this worker authored the intrinsic Hodge/contact/tensor packets and cannot independently accept its own repairs. Historical reviewer identities not present in retained metadata remain unknown. Full-paper PDFs are retained locally only as reading evidence; this report does not authorize republishing them.
