# Independent review of the V13 forward/descent application

Date: 2026-11-08. Reviewer: model worker `/root/restart_hodge_gluing`; the runtime does not expose a reliable model identifier. Target author: `/root/restart_contact_field`. This is a non-author, bounded primary-source and consumer review, not a new theorem, full arithmetic audit, Lean replay, or approval of a future manuscript edit.

## Decision

**Accept the stated bounded application, with the snapshot-provenance clarification below.** The published forward theorem, corrected Cassels–Tate input, finite Kummer inference to the specified class on the actual curves, and point-to-preparation-zero substitutions have the strength claimed in the target record. No mathematical discrepancy was found in that scope. The target's explicit source-coverage and producer gaps remain open.

The controlling target is `recovery-contact-0358/forward-source-review/receipt.json`, SHA-256 `29ce41891589b97b3ab36b129386410d264acc1807908cc322d387cd08aa2a53`, and its `APPLICATION.json`, SHA-256 `5440aca3aaf4a39e82cb09635b6855e12bf53e61777a977b7603274a8ab52715`. All 27 artifact hashes were checked independently, including the primary reading evidence. All eight inherited V11/V13 passages were rechecked byte for byte. The actual target is V13, whole SHA-256 `9db71bbfcefb37db56eabcf40a5f9dd85de9ed58294635da3dbf6d4f5caa8fcd`; the literal contribution remains 318/326, not the new V13 394/411 reduction.

I previously reviewed the separate PP consumer and authored unrelated Hodge and Berger application records. I did not author this forward/descent record, its source acquisition, the two-twist argument, or the pole-normalization modules. I used earlier records to locate the evidence, then read the primary statements and actual consumers and derived the bounded inference. Geometric's separately reported corroboration is not the basis of this decision. Distinct model identities do not eliminate correlated error.

## Primary-source findings

1. **Kolyvagin, published ICM theorem.** The official IMU volume contains the cited article at printed pp. 429–436. I read the modularity definition, Theorems 1–5 and the connecting proof, and finite Kummer equations (4)–(5). I visually checked printed p. 430: Theorem 1 says analytic rank **at most one**, not strictly less than one, despite the OCR. Its output is the algebraic rank and finite **full** Sha. It is not limited to an odd primary part and has no residual-irreducibility or ordinary-reduction hypothesis. The preprint's relevant statements and proof route agree with the published ones. The eight extracted PDF page-content streams independently match official-volume pages 517–524 exactly. This supports replacing the preprint-only source binding with the published ICM statement; no actual citation edit is preapproved.

2. **Gross–Zagier, published nonvanishing input.** I read I.3, I.6.3–6.4, I.7.3 and the V.1 comparison on printed pp. 307–308; I visually checked the formula and height-base correction on p. 230. The odd fundamental discriminant, coprimality and square-modulo-4N conditions agree with Kolyvagin's auxiliary field. The trivial class-group character and the same weight-two newform give the required nonzero Heegner component. The positive factor in I.6.3 is sufficient; no period constant is transported into the final polynomial. I.7.3 alone gives an infinite-order rational point, not rank exactly one or finite Sha. The published height-base and old-form corrections do not change this nonvanishing use.

3. **Poonen–Stoll, with the actual correction.** I read the published elliptic alternating-pairing statement at pp. 1109–1110, the definitions, Corollary 7 and Theorem 8 at pp. 1122–1123, and the author's erratum. I compared the corrected Section 2 in the current author version. The quotient is by the maximal divisible subgroup. The erratum requires finite M[p] to identify it with the infinitely divisible elements; finite Selmer groups and Kummer exactness give this for Sha at every prime. For an elliptic curve the rational origin induces the relevant rational-divisor polarization. General principally polarized varieties at 2 must not be substituted for this elliptic case. A perfect alternating pairing on the finite 2-primary quotient pairs cyclic factors and makes the dimension of its 2-torsion even. The pairing restricted to that 2-torsion need not be nondegenerate and is not used.

4. **BCDT remains explicitly incomplete as a source-version comparison.** I read the literal author Theorem A and the introduction's six modularity equivalences. The document has placeholder publication metadata and is not a final-typeset copy. Its actual-target morphism is from X1(N). Kolyvagin uses X0(N) to the actual E. The rational-newform, J0 quotient and Q-isogeny composition is the identified comparison route, but its authoritative primary-source verification remains open in this packet. I neither relabel an X1 morphism nor infer an integral lattice identification from an isogeny. No denied publisher access was retried or bypassed.

The primary URLs, versions and exact hashes are already preserved in the target `sources.json`, whose hash was checked. I did not perform a new exhaustive errata search. The target's limited negative searches retain exactly that status.

## Nine application obligations

### 1. Source hypotheses

The required curve is an elliptic curve over Q with analytic rank one and the actual modular parametrization, not a curve with merely matching numerical invariants. V13 fixes E_l: y²=x(x−l)(x+3l), l positive squarefree and l=11 mod 12, with discriminant 2304l⁶ nonzero. The computation of Selmer dimension three and RC are retained premises. They supply analytic rank one before the published forward theorem is invoked. Full rational 2-torsion causes no excluded case. The BCDT/X0 source bridge is retained as a source-coverage dependency, not marked closed.

### 2. Constructed objects

The objects are the two actual curves with l=n and nθ, their full Selmer and Sha groups, and the specified class (β,1) in the ordered coordinates (x+3l,x−l). No optimal quotient replaces E_l in Kummer exactness. Finite Kummer gives r+dim Sha[2]=1 because dim E_l(Q)/2E_l(Q)=r+2. After RC and rank one, it gives Sha[2]=0 and hence a representative of this particular class. Finiteness of Sha alone would not imply Sha[2]=0.

### 3. Domain and index coverage

Both l=n and nθ satisfy the RC domain, with n prime to 6θ; θ=1 is permitted. The published theorem applies separately at each curve's own conductor and does not need a uniform auxiliary discriminant, prime, degree or rank bound over the whole family. Finite Kummer uses all local images, including 2, 3 and infinity. The general matrix/CRT/Dirichlet/local-image producer is read for its interface and retained as a dependency, not independently reconstructed or globally accepted by this review.

### 4. Transition and comparison maps

The source route has Sha(Q)→Sha(K), whose kernel is killed by 2 and finite; it does not discard the 2-primary part. The actual Kummer functions and their limiting values at the roots give torsion images (1,1), (l,1), (3,−l), (3l,−l). The finite pole maps are explicit: V=θc² sends the second point to E_(nV) by (x,y)↦(c²x,c³y); dividing both curve parameters by a² and coordinates by a²,a³ makes the first abscissa B and the second Bs². With e=e0/B, p=y1/B, q=y2/(B²s), h=e(B−b²), the identity e0V=B²h gives precisely the two displayed conics.

### 5. Identity of the consumed object

Before RC, finite 2-torsion implies Sha[2∞]=(Q2/Z2)^t⊕F with finite F; equivalently its compact dual is finitely generated over Z2. The alternating finite quotient forces dim F[2] even. Thus r+t+dim F[2]=1 gives F=0 and the full Selmer corank r+t=1, not already algebraic rank one. After RC the representative of (β,1) is obtained on the same E_l. It need not be the Heegner point used by the published rank theorem. This distinguishes the full primary object, its finite quotient, and the selected finite Kummer class.

### 6. Coefficients and normalizations

The curve coordinates are rational; squareclasses and finite Selmer dimension are over F2; corank is over Z2. From the cubic, the selected point has [x]=β. The preparation-zero B is 17b, and its second conic has **B h**, not h. Passing to the old finite component changes its e-coordinate to B times the manuscript e, leaving p,s,q unchanged. Passing next to ThreeHelper changes old e,s,q to b times the new e,s,q, leaving p unchanged. These are distinct substitutions. I read the two actual normalization modules and the literal builder and verified the residual factors b and b³ in the ThreeHelper step. No integral isogeny statement or exact Gross–Zagier metric normalization is consumed.

### 7. Local conditions

I checked the role of all local conditions and the particular class's small-prime sufficiency. β=1 mod 8 makes (β,1) trivial at 2; at 3 it is the first torsion class; positivity handles infinity; mutual squareness and the retained support equations handle support primes. Necessary dyadic valuation parity is not used as sufficient membership for arbitrary classes. For preparation zero, b>0, square reduced denominator, the three local square hypotheses and v2(b)≥3, v3(b)≥1, v17(b)≥2 make V=B²(1−b/17)>0 and locally square. At primes of β outside the exceptions, the odd valuation of b is positive; at primes of θ, odd v(V) forces v(b)=0 and B=17² modulo that prime. Thus the mutual-square and disjoint-support input to the two-twist lemma is the actual one.

### 8. Exceptional cases

β is nonsquare; the fresh q0 makes β/l nonsquare on both supports; and −l is negative. Thus (β,1) differs from all four 2-torsion images, so x,y,x−l,x+3l are nonzero. The choices divide only by nonzero B,a,c,s. The θ=1 case can reuse the point. The parity variant permits U=0; the preparation-zero completeness theorem requires b≠0. The finite polynomial normalization separately handles b=0 by explicit witnesses. No guard on arbitrary polynomial solutions is introduced by divisions made only while constructing these nonzero completeness witnesses.

### 9. Downstream consumption

I read actual V13 RC/corank/forward lines 1090–1194, simultaneous realization 7787–7890, parity/scaling 7892–7940, preparation zero 10563–10635, the literal builder's pole block 643–686, and the scalar-local/final-completeness prose. The two normalization components carry these conics to the actual builder. The conditional scalar check for a=114444r and b=a(W/(1+a))² is valid given one W with 0<W<2 and the required units. That W must be compatible with the point, prime-ray, guard and anchor choices. This review supplies no such simultaneous assignment. The target remains one assignment to all 288 source rows; the finite canonical 326 lift adds no arithmetic premise. Acceptance here is not full RC, full PP, full 318 completeness, or a PEL/height conclusion.

## Snapshot clarification and current delta

The target records observed HEAD `09e35ad61946e92561460d93c3e57831ea5e3117`, but its controlling arithmetic.md hash `9737d56476c98677624725fc61bb36433ed008b2636a22d423cef8c1c02ee518` is not the blob at that HEAD. It is the then-present reviewed snapshot, preserved exactly as `docs/quartic-318-326/v13-consumer-binding/arithmetic.before.md`. I verified both target excerpts against those preserved bytes. The immutable target is not rewritten, and the HEAD is not treated as a substitute for the actual hash.

The subsequently integrated arithmetic.md, SHA-256 `069738d42a127a2cd3a476cba9281a77f3cbd23ec81a5a3441090ea8ebab09d0`, changes only the Kato section title, its baseline paragraph, and the new distinction between V12/V13 reductions and literal 318/326. I compared the full delta. The scalar-local excerpt, the subsequent source/representation/class discussion, and the exact final 288-row target remain unchanged; later paragraph line numbers shift by two. This observation is a bounded consumer comparison, not a replacement acceptance of that separate adoption record. `CHECKS.json` records both snapshots and the observed current HEAD.

## Remaining work and integration limits

- Incorporate the accepted published Kolyvagin/correction evidence through a separately reviewed exact citation change; this report approves no hypothetical edit.
- Preserve BCDT final-typeset/corrections and the authoritative X0-to-actual-E quotient-source coverage as open in this packet.
- Independently audit the complete local Kummer/matrix/CRT/Dirichlet producer and RC; the present finite inference is conditional on them.
- Supply the one compatible arithmetic witness construction and all 288 rows. Do not merge separate existence arguments into a simultaneous conclusion.

Only this report, `CHECKS.json`, `replay_checks.py` and `acceptance.json` are public review artifacts. Third-party PDFs and rendered reading evidence are excluded. No shared source, manuscript, branch or proof module was edited, and no compiler was run.
