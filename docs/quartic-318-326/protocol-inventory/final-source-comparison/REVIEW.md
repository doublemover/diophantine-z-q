# Supplement: final published Gaudron–Rémond comparison

Date: 2026-11-08. Reviewer: `/root/restart_hodge_gluing`.
This supplements, without modifying, the earlier Hodge/Arakelov application inventory receipt `3705dc548a8f9cacfc7a21991849f7c0fee5bef73ec324a7949fe8e8a0c7358d`.

## Completed comparison

The final publication is Éric Gaudron and Gaël Rémond, *Nouveaux théorèmes d'isogénie*, Mémoires de la Société Mathématique de France 176 (2023), vi+123 pages, DOI https://doi.org/10.24033/msmf.484. An ordinary web search located the openly indexed official full PDF at:

https://smf.emath.fr/system/files/filepdf/smf_mem_176_0.pdf

This is the full 136-PDF-page publication, not the restricted excerpt or an author manuscript. It was retrieved through normal access; no restriction was bypassed. SHA-256: `b1e2e32bec626cf6d27fb7d6d8702b5c707e0c3dc002d979088e62d8cda514a4`.

I read §1.5 and Theorem 1.9 on printed pages 7–8 (PDF pages 15–16), including their definitions, and visually checked both pages. I compared them to the September 2022 author PDF https://lmbp.uca.fr/~gaudron/art20.pdf, SHA-256 `4ac73d953938fb6ceb5b2359fdfa7de85456d15b9a03d26e4237faede14b05d8`, §1.5 on printed pages 14–15. At the consumed statement/definition level they agree:

- The height is the stable Faltings height with Faltings's original normalization.
- For an abelian variety A of dimension g over a number field K, Xi(A)=((7g)^(8g²)[K:Q] max(1,log[K:Q],h_F(A)))^(2g²).
- If A and B are defined over K and become isogenous over an extension L/K, Theorem 1.9(1) gives isogenies in both directions over L, each of degree at most Xi(A)².
- The stronger Xi(A) alternative needs A_L to be MM. The project uses the general squared bound and does not need to identify CM type with the separate MM condition.
- No polarization-degree hypothesis is present in the consumed assertion.

Publication changes visible here include repagination and numeric rather than author-key bibliography references. I do not claim a byte-for-byte or whole-monograph equivalence, a rereview of the theorem's proof, or an exhaustive independent erratum search.

## Exact application consequences

V11 `manuscripts/quartic_v11.tex`, whole SHA-256 `1210d2e6f409e502fc9c95afc248fac16a9df48c760a396143780c20ec80b662`:

1. Lines 7470–7481 and 9042–9050 use source J or J_H over the stated field and the general g-dimensional bound. Half the logarithm of Xi² is log Xi, yielding precisely the written factor 2g² times (8g² log(7g)+log d+log max(...)).
2. Lines 7634–7653 use the dimension-two source A' over L itself. Substitution g=2 gives Xi(A')=(14^32 d max(1,log d,h_F(A')))^8; half-log variation from Xi² gives the displayed factor 8. The author explicitly avoids the MM shortcut.
3. Current contribution `quartics/quartic-318-326/docs/arithmetic.md`, lines 1419 and 1437–1455, uses the actual dimension-two image C_A as source. Its 8*(32log14+log d'+log max(...)) is the same specialization. The text bounds the original-height maximum by the larger shifted-height maximum and uses equal-dimensional isogeny variation, for which a dimension-linear shift cancels.

This closes the earlier **GR selected-author-to-final-statement comparison** and verifies the displayed constant/normalization specialization. It does not construct the actual image, its dimension, the required same-field isogeny, or the geometric/metric producers. Those are application obligations retained in the earlier inventory. In particular, the V11 large-Jacobian R^19 route and the current dimension-two-image 49/8 route are different applications.

The reviewer authored the earlier Hodge inventory and some intrinsic algebraic Hodge predecessors. This supplement is a primary-source comparison, not independent acceptance of that reviewer's own application repair. It may be independently consumed by the integration reviewer.

## Rémond: precise remaining limitation

Gaël Rémond, *Propriétés de la hauteur de Faltings*, Annali della Scuola Normale Superiore di Pisa, Classe di Scienze 23(3) (2022), 1589–1596, DOI https://doi.org/10.2422/2036-2145.202010_062, is a published work. Publisher metadata is at https://journals.sns.it/index.php/annaliscienze/article/view/5695. The journal's PDF route leads to subscription access. Normal searches of the exact title, DOI and author/repository sources did not supply a legitimate final-typeset copy in this pass. I did not try alternative endpoints to bypass that restriction.

The June 2021 author copy https://www-fourier.univ-grenoble-alpes.fr/~remond/2476.pdf, SHA-256 `e23a019a7432e299014ead57a1ba51c3945b8351a64c96f339536786c8f79c5d`, has been read: Corollary 1.2 bounds h_F(B)+h_F(A/B) by h_F(A) for an abelian subvariety B defined over the same number field, and the next page explicitly extends the three statements to stable height. The inequality is invariant under dimension-linear normalization shifts. This is exactly the author-version input in the current dimension-two image application, but author-to-final equivalence has **not** been checked. Publication metadata is not substituted for that comparison.

Accordingly, the Rémond final-version task is **incomplete**, not a mathematical rejection or a claim that the theorem is unpublished. Resolve through an authorized final copy or retain this limitation. No full application acceptance, PEL result, or overall height proof follows from closing the separate GR version check.

## Deliverable handling

Local PDFs and page renders are reading evidence only. They are excluded from the public deliverable. `receipt.json` binds their hashes and the source/consumer passages. The public packet contains this review and metadata, not redistributed third-party PDFs.
