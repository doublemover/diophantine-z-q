# Independent review: Pan's modularity application in Version 11

Reviewer: `/root/restart_modular_curve`. Date: 2026-11-08.
Target: `manuscripts/quartic_v11.tex`, SHA256 `1210d2e6f409e502fc9c95afc248fac16a9df48c760a396143780c20ec80b662`.
The reviewer did not author the V11 Pan/scalar-descent text or the retained Pan publication packet. This is a bounded independent source/application review, not an independent reconstruction of Pan's 137-page proof or of the full quaternionic geometric producer.

## Decision

**Accept the stated Pan theorem interface and its use at p=5, relative to the explicitly identified representation-construction and de Rham inputs.** The actual source theorem covers continuous irreducible odd two-dimensional representations of G_Q, unramified outside finitely many primes, potentially semistable at p, with distinct Hodge–Tate weights. At p=5 it imposes no residual-image proviso. Its conclusion is a cuspidal eigenform **up to twist**. The manuscript does not legitimately obtain a conductor bound, a bounded coefficient field, or bounded same-field GL2-type descent merely from Pan, and this review imports none.

**Do not mark the authoritative JAMS version-of-record comparison complete.** The current DOI request returned HTTP403. The inspected primary theorem/proof version is arXiv:1901.07166v2, and the independently inspected published corroborating statement is Calegari's ICM chapter. Their scopes agree. Neither establishes textual identity with the inaccessible JAMS article. This is an explicit evidence limit, not a discovered false theorem.

**Do not infer unconditional acceptance of the entire H5/318 arithmetic application.** The actual QM surface, controlled scalar descent, de Rham comparison and finite-extension descent, conductor estimates, modular-Jacobian transfer and height comparison are separate inputs/arguments. The group's current Brinon–Conrad review owns the de Rham source/descent check. The level-repair text itself retains a global-review/published-Pan pending marker, which this bounded review does not silently erase.

## What was freshly verified

1. Pan arXiv v2 was retrieved from its explicit versioned URL. SHA256 `590171129d28a65749cf92b1f6099dbacaa90cc6698828f0a4dfd3da943f4824`, exactly the prior source pin. The arXiv record still lists v2, 3 September 2021, as the latest version.
2. Conjecture 1.0.1 on PDF page2 supplies the continuity, irreducibility, finite ramification, potential semistability and oddness conditions. Theorem1.0.4 on PDF page5 adds distinct weights and an extra local residual condition **only when p=3**. At p=5 this additional condition is vacuous.
3. Pan's notation on PDF page7 assigns the cyclotomic character Hodge–Tate weight −1 and sends uniformizers to geometric Frobenius in local reciprocity.
4. Calegari's official EMS published PDF was freshly retrieved, SHA256 `d8e9a3ec3f2a4bedd674d95cf5f1e03fe26a67745c6f1cadf39b3fbf9e004cb5`, exactly the prior pin. Printed pp611–612 supply the continuous irreducible geometric context; p624 states the full regular result for p≥5, odd and with distinct weights, up to twist. This is a published mathematical formulation, not just a bibliography entry, but it is not a separate proof of Pan's theorem. The chapter's reference137 cites Pan's arXiv paper.
5. Fresh Crossref metadata identifies the authoritative JAMS article, DOI10.1090/jams/991, vol35 (2022), pp1031–1169, and its version-of-record URL. Its relation object is empty and no update-to/updated-by field is present. Targeted correction/erratum searches and the current arXiv revision record did not reveal a correction to this interface. This limited search does **not** prove that no correction exists.
6. The JAMS DOI fetch returned403. No access restriction was bypassed and no AMS PDF hash is invented. The retained Newton published corroboration was read as a prior report, not freshly re-inspected, so it is not needed for this review's decision.

## The two actual V11 applications

### Baseline height argument

The non-CM case starts with `End^0(A_Qbar)=B`, not merely some QM subalgebra. The chosen B-compatible isogenies μ_σ and positive scalars a_σ=(deg μ_σ)^(-1/4) give a sign cocycle. The root-of-unity cochain β corrects it. A common number field C contains all finite coefficient data and splits B. For each coefficient prime ℓ the manuscript constructs

`ρ_ℓ(σ)=β(σ)^(-1) a_σ μ_σ ∘ σ`.

This is the actual representation of G_Q, not the uncorrected projective action. It commutes with B, and matrix units split it as `r_ℓ ⊕ r_ℓ`, with r_ℓ two-dimensional. Its restriction over the kernel field L′ is the actual Tate action of A, and `a_σ=1, μ_σ=1, β(σ)=1` there.

Faltings semisimplicity and the exact endomorphism algebra imply that the multiplicity summand has scalar commutant and is absolutely irreducible on G_L′, hence on G_Q. The finite coefficient data and the continuous Tate action give continuity. The de Rham lemma applies to the actual finite-extension restriction and proves weights {0,−1}, using proper-smooth comparison, duality, direct summands and finite descent. Berger then gives potential semistability. These are explicit dependencies, not consequences of knowing the weights alone.

Oddness is checked on the actual multiplicity space: antiholomorphic conjugation composed with μ_c exchanges the two Hodge summands, each a simple M2(C)-module. Its multiplicity action is nonscalar; after scalar correction its square is1, so eigenvalues are1 and−1. This does not assume oddness of an unconstructed residual representation. Finite ramification is supplied by the controlled support T and good reduction.

Pan is applied once at ℓ=5. The source conclusion is then processed by the manuscript's separate character argument: the twist is a de Rham subrepresentation of a Hom representation; its weight is integral; comparing the two multisets with the modular weights forces modular weight2 and twist weight0. The baseline invokes Conrad's local/global character argument for finiteness. That Conrad application is not freshly source-audited here; it is not part of Pan's theorem.

### Level-repair argument

The second application begins with a non-CM surface over the constructed normal fiber field L, degree dividing576, with all geometric homomorphisms defined over L and exact geometric endomorphism algebra B. Here B is the division quaternion algebra of discriminant210, and R=B_*M(s), T={p:p|R}. It constructs the same type of corrected representation using b rather than β.

The passage explicitly cites Calegari's published formulation and the detailed Pan author theorem, and explicitly disclaims final-journal identity. Its p=5 application has the same hypothesis match. It does not require a residual reducibility assumption; Pan's Theorem1.0.4 combines the residually reducible and irreducible cases.

The level-repair passage gives an independent finite-twist argument after modularity. From `ρ_5|G_L′=V_5(A)` and `ρ_5=r_5⊕r_5`,

`(det r_5)^2=χ_cyc²` on G_L′.

Thus det r_5/χ_cyc has finite image on an open finite-index subgroup, hence globally. The modular weight2 determinant divided by χ_cyc also has finite image. The square of the twisting character consequently has finite image, so the character itself has finite image. This does not require a uniform bound on its order. Its finite twist can be absorbed into a primitive weight2 newform f.

This argument is a valid finite-image argument for the literal characters; it is not an inference that every Hodge–Tate weight-zero representation has finite image. The weight comparison and determinant calculation are separate from Pan's theorem and must remain visible.

## Exact downstream consumer

The first output is an isomorphism class of two-dimensional modular representation, in the Tate convention. Li's Fricke relation and Shimura's Jacobian construction are separate inputs producing the relevant modular abelian-variety/J1(N) constituent. No family of arbitrary finite fibers substitutes for that constituent.

The manuscript transfers the coefficient-prime realization from5 to3 using algebraic Frobenius traces of the same scalar-corrected endomorphisms. This is a separate compatible-system argument. **Pan is not reapplied at3.** Therefore its p=3 residual exception is not a missing condition in the conductor-at5 calculation. The three-adic realization is used at5 and the five-adic realization at the other primes.

The equality of primitive newform level and the local conductor uses Carayol and Casselman, not Pan. It includes nebentypus, dyadic places and monodromy. Tate/cohomological duality and unramified normalization twists preserve conductor. Those source applications have their own obligations.

Over L′, the common constituent of A and J1(N), combined with Faltings' Hom theorem and Poincaré reducibility, gives the actual isogeny `A×Z→J1(N)`. This is consumed by modular-Jacobian height estimates and isogeny-height bounds. The coefficient field and scalar character order may vary. The manuscript expressly avoids asserting bounded same-field descent to a rational GL2-type variety.

The Pan step consequently supports the non-CM modular-height route. It does not prove the global arithmetic/analytic identification of the literal final contact source, discharge PP or RC, or remove sourceArithmetic from the final Lean bridge.

## Nine-obligation record

`APPLICATION.json` records all nine obligations with required/constructed/match/evidence entries. `BINDINGS.json` pins the exact V11 target, both construction/application passages, de Rham interface, downstream transfer and retained publication qualification. `SOURCES.json` distinguishes actual freshly retrieved bytes, authoritative inaccessible journal text, published corroboration, and limited correction searches. No source is relabeled final-published merely because it has a journal reference.

## Remaining precise gates

- JAMS final theorem/convention/proof comparison remains uncompleted because of403. An authorized accessible copy is the smallest missing input for that exact requested comparison.
- The de Rham descent acceptance remains a separate current review; this packet takes only its exact stated interface and does not convert a Hodge–Tate-only assertion into de Rhamness.
- The baseline Conrad finite-character source application is not freshly checked here; the level-repair determinant proof is separately checked and does not automatically amend the baseline text.
- Construction of the particular QM surface and controlled scalar descent, modular conductor/realization comparison, and actual contact-source/height identity are not certified wholesale by this bounded Pan review.
- Neither the retained pending-review comment nor the broader current318 status should be removed solely on the basis of this decision.
