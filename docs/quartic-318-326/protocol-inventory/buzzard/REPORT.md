# Buzzard's corrected integral-model application in Version 13

Reviewer: `/root/restart_group_law`. Date: 2026-11-08. This is a fresh, bounded internal-model review of the existing application, not a manuscript edit, a kernel proof, or whole-proof acceptance. The reviewer did not author the reviewed V13 passage or the historical A002 argument. The machine-readable manifest binds the exact manuscript, source metadata, nine obligations, historical argument and downstream excerpts.

## Finding and actual scope

The corrected Buzzard Theorem 2.1 / Corollary 2.3 application at **V₁(5), discriminant 6, over Z[1/30]** is valid. The subsequent finite-marking and free-quotient argument produces the stated full-three integral moduli scheme and the same universal abelian surface. No additional exceptional prime or auxiliary-five degree factor was found. This construction is already justified in the earlier geometry report and incorporated in V13; it is not a newly supplied repair.

**The literal 318 height dependency is different.** V13 lines 6825–6829 expressly distinguish the six-contact theorem. The five-contact proof uses discriminant 210 and Yuan's integral moduli input at lines 6940–6962. Its construction is reused at lines 8935–8958, and the contribution's height49/8 argument retains its level estimate and actual dimension-two surface. A sound Buzzard/discriminant-six application is not acceptance of Yuan/discriminant-210, nor of the five-contact height theorem or all 318 source arithmetic. The source-specific completeness assembly explicitly does not use the global contact-height bound.

## Source version and inspection

Freshly retrieved the [author's corrected PDF](https://www.ma.imperial.ac.uk/~buzzard/maths/research/papers/shimura.pdf), 231,177 bytes, SHA-256 `4854cb4adc99fec7eac47596dea86832e2e468f3c80d78726afeb98d2404b915`. It matches the historical pin exactly. Its title page dates the original to 13 May 1996 and the typo corrections to 14 June 2002. Read §§1–2, pages 2–7, including definitions of levels, the hypotheses preceding Theorem 2.1, the full proof of Lemma 2.2, and Corollary 2.3 and its proof. Pages 3, 5 and 7 were additionally inspected visually.

The [author's publication list](https://www.ma.imperial.ac.uk/~buzzard/maths/research/papers/index.html) identifies the published article as *Duke Mathematical Journal* 87(3) (1997), 591–612, and links this corrected author copy. Crossref's publisher-deposited record confirms [DOI 10.1215/S0012-7094-97-08719-6](https://doi.org/10.1215/S0012-7094-97-08719-6). The journal download returned an Incapsula unsuccessful-request HTML page, not a PDF. No access bypass was attempted. Thus this review checks the actual **corrected author version**, not a fresh byte comparison to the 1997 typeset article. The author's page and bounded publication/correction searches did not identify another correction to these statements. The header does not itemize its typo changes; no invented claim about their precise location or harmlessness is made.

Also freshly read the statement and proof of [Stacks Lemma 66.14.2, tag 07S7](https://stacks.math.columbia.edu/tag/07S7). It supplies the scheme quotient and torsor bridge for the actual free action. Only the report and metadata are deliverables. Third-party PDFs, extracted text, screenshots and HTML cache are not public artifacts.

## Required input versus the constructed object

Buzzard fixes an indefinite nonsplit rational quaternion algebra D, a maximal order, and an element t with t²=−disc(D). The false elliptic objects are abelian surfaces with an injective action of that order over bases where the discriminant is invertible. The chosen involution determines their canonical principal polarization. The source's full marking is **left-order-linear**, and changes of marking use **right multiplication** on the source module. Neither a chosen symplectic determinant component nor a matrix-algebra identification at a division prime is implicit.

The manuscript fixes B=(2,−3), its maximal order O=Z[i,(1+j)/2], and μ=2j+ij. The displayed μ satisfies μ²=−6, and its Rosati formula is exactly the source formula. The maximal-order/discriminant and positivity identification are the retained A001/Baba–Granath/Lin–Yang predecessors; their earlier actual argument was read, but their primary publications are not freshly re-audited here.

For U=V₁(5), all three source requirements are met:

1. **Full reduced-norm/determinant image.** At the split prime 5, matrices diag(a,1) realize every unit determinant and belong to V₁(5). At other split primes the level is all maximal-order units. At the division primes 2 and 3 the reduced norm on maximal-order units is onto Z_p^×: an unramified quadratic subfield suffices, with residue norm onto and successive principal-unit norms onto by the residue trace. Thus the global compact subgroup has the required full product image.
2. **Maximal level at every division prime.** Only the split prime 5 is changed. At 2 and 3 the subgroup is O_p^×. A level-three congruence subgroup would fail this requirement; the manuscript never substitutes it into Buzzard's theorem.
3. **Smallness.** U is V₁(N) itself with N=5≥4 and gcd(N,6)=1. Its smallest defining full level M_U is 5: V_5 is contained, whereas a modulus prime to 5 leaves an unrestricted component at 5. Hence the actual source base is exactly Z[1/(M_U·6)]=Z[1/30].

Theorem 2.1 first yields a proper smooth relative-dimension-one **stack**. Lemma 2.2 removes stabilizers under the smallness hypothesis; Corollary 2.3 then gives a regular projective **scheme** representing that same moduli problem. The universal abelian surface therefore exists over the whole integral base, not merely on its generic fiber. There is no conclusion at residue characteristics 2, 3 or 5 from this application.

## Markings, comparison maps and exact final object

Write X₁ for the starting V₁(5) scheme, X₅ for its full-five refinement, and X₃₅ for the added full-three refinement. The actual maps are

- X₃₅ → X₅ → X₁, forgetting first the three-marking and then replacing a full five-marking by its V₁(5)-orbit;
- X₃₅ → X₃ = X₃₅/G₅, forgetting only the five-marking, with G₅=(O/5O)^×.

The first full-five refinement uses precisely the orbit-sheaf construction of Buzzard §1. Étale locally the universal finite torsion modules are constant; choices of compatible full markings form finite étale torsors. All choices are retained. Full-five's determinant image need not remain full, so it would be incorrect to reapply the theorem or Proposition 2.5 to that level using the original hypotheses. Instead it is the finite cover of the permitted starting scheme. This includes every determinant component.

At three, B₃ is a division algebra, not M₂(Q₃). For every geometric fiber of the base (all characteristics different from 3), V₃(A) has Q₃-dimension four and a faithful unital B₃ action, so is one-dimensional as a left B₃-module. If Λ is its O₃-stable Tate lattice and x∈Λ has least division valuation, every y∈Λ has yx⁻¹∈O₃. Thus Λ=O₃x; reduction modulo 3 gives the exact free rank-one O/3O-module needed for Isom_O(O/3O,A[3]). The sheaf is consequently nonempty on every geometric fiber and finite étale. This proves the claimed full-three cover without applying the source's prime-to-discriminant level definition outside its domain.

A geometric stabilizer of the G₅ action on X₃₅ supplies an O-linear automorphism of A preserving the canonical polarization and the full three-marking. The polarized automorphism group is finite. Its faithful action on T₃(A) is congruent to identity modulo 3. The group 1+3M₄(Z₃) is torsion-free: a nonidentity element of prime order q, with first displacement 3^aC, has a nonzero first term after raising to q (valuation a if q≠3, valuation a+1 if q=3). Hence the automorphism is identity; the full five-marking then forces the stabilizing group element to be identity. Since the constant group is étale, this geometric check gives the free scheme action. In this case |G₅|=|GL₂(F₅)|=480, supported on the already inverted primes; in any event the free-torsor quotient argument does not require a separate tame-action inference.

Stacks 07S7 applies to the projective X₃₅ and this finite locally free constant group. It gives a scheme quotient and a G₅-torsor; the latter is finite étale. Smoothness and properness descend. Tensoring the translates of an ample bundle gives a canonically linearized ample bundle descending along the torsor, so the quotient is projective. The abelian surface, O-action, canonical polarization and three-marking have their tautological descent datum because changing five alters none of them. This is effective descent for the polarized abelian scheme.

Most importantly, X₃ is the **same full-three moduli functor**, not merely a related finite cover. Given any three-marked family, its full-five marking sheaf is the G₅-torsor that produces the local lifts to X₃₅; forgetting five descends those lifts back to the original family. Conversely quotienting a lifted object erases exactly five. These constructions commute with arbitrary base change. The full-three marking eliminates automorphisms, so no residual gerbe or multiplicity remains. Its generic fiber is therefore the manuscript's entire Y₃. The prior bound deg(Y₃→P¹_j)≤324 is neither multiplied by 480 nor obtained anew from Buzzard.

## Downstream boundary and history

The immediate six-contact consumers are V13 lines 556–605: extension of the normalizer action to the smooth proper model, tame branch persistence at p>324, normalized pullback along J(u), and good reduction for the pulled-back surface. All such primes lie in the base Z[1/30]. The arbitrary-point universal-family identification above is precisely what permits this use. Stable-model uniqueness, branch persistence and normalization calculations remain the separately argued A078 input. This review read that historical argument and the current consumer; it does not replace a fresh review of all its external sources or certify the later modularity/height estimates.

The actual earlier `parallel-geometry-report.md` A002 proof was read, not merely its status label. It already checks the three hypotheses, division-module lattice, full marking sheaves, free quotient and descent. Its quoted pre-integration whole-manuscript hash differs from the current archived audited baseline; this is not concealed by a hash refresh. The entire current V13 model-construction excerpt is a unique byte-identical occurrence in both V11 and the archived audited baseline, as recorded by the manifest. Historical justification is therefore **found** and current incorporation is **present**, while the unchanged dependencies remain named.

For literal 318, the relevant five-contact model is the one with discriminant 210, all level-three components, field degree at most 576, and support outside 210. It is not this discriminant-six degree≤324 construction. V13 explicitly says so before the five-contact theorem and explicitly reuses the five-contact geometric construction for the improved height. The contribution's current height49/8 derivation uses N≤210^300 R² and that same A. Its soundness still needs the full height/modulus transfer; completeness uses RC/PP and local assembly, not this height estimate. No proof obligation for the actual 318 arithmetic is silently closed by this result.

## Remaining boundaries

- No mathematical defect found in the bounded corrected-source application or the exact integral full-three bridge.
- The publisher typeset bytes were not obtained; corrected author bytes were freshly verified, and published metadata was corroborated.
- No fresh acceptance of the A001 primary-source identification, the full A078 branch analysis, Yuan's distinct model, modular realization, quantitative height transfer, RC/PP, or the 288-row arithmetic witness assembly.
- No manuscript/source code changes, no branch/PR actions, no compiler replay. Historical records are untouched.
