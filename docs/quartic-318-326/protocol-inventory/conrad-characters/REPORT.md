# Conrad local-character application: Version 13, with exact Version 11 comparison

Reviewer: /root/restart_group_law. This is a distinct internal model source/application review. No shared manuscript, application register or branch was edited.

## Result

No repair is required to the local-character step in the current Version 13 argument, lines 835–843, corresponding exactly to V11 lines 828–836. The actual twisting character is defined over a finite coefficient field, occurs as a de Rham line in a Hom representation, and has finite ramification. Conrad's local algebraicity statement applies at the base field Q_5. Removing one integral cyclotomic power leaves a global finite-order character, by the local inertia checks and global class field theory. Comparing the actual Tate weights forces that power to be zero and the modular weight to be two.

The source's sign convention is explicitly reconciled below. Its author-preprint status is retained. The separate companion determinant argument is not substituted for this earlier character argument. Pan, the actual construction and de Rhamness of r_5, standard modular-representation inputs, and the subsequent finite-character twisting/newform and Shimura/Li steps remain separately named dependencies.

## Primary sources and version status

1. Brian Conrad, *Lifting global representations with local properties*, author version dated December 11, 2011, https://math.stanford.edu/~conrad/papers/locchar.pdf. Fresh download: 528,777 bytes, SHA-256 `782fe71a3c7f26ccd67943d468f73540d384e2de5d474bf8369475b8b631d9bd`. These are exactly the prior project pin. I read Appendix B, Definition B.1 and its following assertion, the arithmetic-Artin convention, Lemma B.2 and Proposition B.3 with its proof, printed pp.32–34. I visually checked pp.32–33. The current author webpage still links this file. Targeted publication/errata searches did not identify a replacement journal version or a separate correction to this assertion. This is a bounded check, not a claim of exhaustive absence. The manuscript accurately calls it an author preprint.

2. The paragraph following Definition B.1 explicitly invokes Tate's theorem via Serre, rather than giving a new self-contained proof of local algebraicity. I therefore also inspected the accessible published-book scan of J.-P. Serre, *Abelian l-Adic Representations and Elliptic Curves*, Addison-Wesley 1989 reprint of the 1968 book, hosted by McGill. SHA-256 `971dbfdd4414d99ea21d7d0af63dbb790d7b1188e9aec37f422181a2b543dec4`. Chapter III, Appendix A.6, corollary to Proposition 6, printed III-50, and A.7 Theorem 3, printed III-52–53, state and prove the relevant equivalence between local algebraicity and Hodge–Tate type with semisimple inertia. I visually checked the corollary and theorem. This is additional published-source corroboration, not an assertion that the 1989 scan is byte-identical to Conrad's cited 1998 edition or has identical numbering throughout.

3. For the explicit global step I freshly retrieved Milne, *Class Field Theory*, version 4.03, August 6, 2020, https://www.jmilne.org/math/CourseNotes/CFT.pdf. SHA-256 `50d79af78250a9f1117ad9d337e0b231704a533fc707966ed1bfa52e13d498f5`, exactly the retained project pin. Chapter V Theorem 1.7, p.150, proves finiteness of ray class groups; Proposition 4.6, p.173, identifies their idele quotient; Remark 5.7(a), pp.179–180, gives the global reciprocity map onto the maximal abelian Galois group of a number field. These actual statements, not Chapter VIII's differently numbered Chebotarev theorem, support the present step. I read them and their adjacent explanations and visually checked pp.150,173,179. These are author course notes, not relabelled as a journal publication.

## Exact constructed character and maps

Write S for the modular representation supplied by the separately reviewed Pan conclusion and choose a twisting isomorphism T so that

`r_5(g) T S(g)^{-1} = eta(g) T`.

After a finite extension of Q_5, the matrices of r_5 and S and the finitely many entries of T all lie in one finite coefficient field E. A fixed nonzero entry of T expresses every eta(g) as a ratio in E. Thus the character really is E-valued; this does not assume that an arbitrary Qbar_5-valued character automatically has a finite field of definition.

The E-line spanned by T inside Hom_E(S,r_5) carries eta. It is a G_Q-subrepresentation. Since both ambient representations are de Rham at five, closure under duals, tensors and subobjects makes this line de Rham there. At every prime where both ambient representations are unramified, the displayed equality makes eta unramified as well. Hence its ramified set is finite. These are precisely the character properties consumed by the V13 paragraph.

Conrad's local base L is Q_5 here, while his coefficient K is E. Local algebraicity gives an algebraic map G_m to Res_{E/Q_5} G_m near 1. Since L=Q_5 has only the identity embedding, its local formula has a single integer exponent. In Conrad's arithmetic-Artin normalization it may be written

`eta(Art_Q5(u)) = u^(-n)`

on an open subgroup of Z_5^*. The cyclotomic character has the same unit formula with n=1. Therefore eta_0 = eta * chi_cyc^(-n) kills an open subgroup of inertia at five.

Conrad calls Q_p(1) weight +1: the semilinear line C_L(w) has weight w. The manuscript instead explicitly uses Tate weight -1 for Q_5(1). Accordingly, the above exponent n gives manuscript weight -n. This sign translation is essential when reading the source; it changes neither the actual character nor the final zero-exponent conclusion.

For every q != 5, the image of eta_0 is contained in O_E^*: a continuous character of the compact group G_Q has zero valuation. Local reciprocity identifies the relevant abelian inertia with Z_q^*. Its pro-q subgroup has finite image in O_E^*, which has an open pro-5 subgroup. Indeed their intersection is simultaneously pro-q and pro-5 and hence trivial, so the pro-q image injects into the finite quotient by that pro-5 subgroup. The remaining residue-unit quotient is finite too. Thus eta_0 has finite inertia at every such q, including q=2.

Only finitely many q are ramified. Choose a finite modulus with sufficiently deep unit subgroups in the kernels at those q and include the real place. The pullback of eta_0 along global reciprocity kills these unit groups, all units outside the finite set, positive real elements and Q^*. Milne's idele description then makes it factor through the finite ray class group for that modulus. Surjectivity of reciprocity onto G_Q^ab proves eta_0 itself has finite image. Merely having finite inertia at each prime would not by itself justify a global conclusion without this finite-support and reciprocity argument.

Finally, in the manuscript's convention the modular weights are `{0,1-k}` and the cyclotomic power shifts both by -n. Equality with the actual r_5 weights `{0,-1}` gives

`{-n, 1-k-n} = {0,-1}`.

The modular holomorphic weight k is at least one. Its gap is k-1, so k=2; then the largest weight is -n=0, giving n=0. Thus eta is already finite order. No arbitrary scalar, unidentified character, or changed local representation is passed to the next consumer.

## Nine-obligation review

1. **Source hypotheses.** Conrad requires a continuous character of G_L^ab with finite local base L/Q_p and finite coefficient field. Here p=5, L=Q_5, and the finite coefficient field E is justified by the fixed twisting isomorphism. Its underlying Q_5 representation is Hodge–Tate because it is de Rham. Semisimplicity over Q_5 follows by splitting the separable coefficient field into character lines; this also verifies the inertia condition in Serre's general theorem.

2. **Constructed object.** The line is the actual eta-equivariant line spanned by T in Hom(S,r_5). The construction identifies eta itself, not merely a character with the same weights or ramification. The finite character eventually absorbed into the form is this same eta.

3. **Domain coverage.** Local algebraicity is used only at Q_5, where a single exponent suffices. The argument does not incorrectly replace all locally algebraic characters over a larger local field by cyclotomic powers. The remaining finite primes, including two, are all covered by the pro-q/pro-5 argument, and the real place is included in the modulus. There is no omitted infinite set of newly ramified primes.

4. **Transitions and maps.** The maps are the Hom-line embedding, local arithmetic-Artin map on units, exact multiplication by chi_cyc^(-n), and global reciprocity followed by the ray-class quotient. All arrows use the same eta and the stated field E. The coefficient embeddings and sign change do not introduce a replacement representation.

5. **Limit or final identity.** No Euler-system or new inverse-limit argument is involved. The endpoint is the equality eta = eta_0 * chi_cyc^n as global characters, with eta_0 finite and then n=0. Thus the next form-twisting step consumes a finite character giving the original r_5, not an unspecified proportional or potentially equivalent object.

6. **Coefficient conventions.** Finite E may be larger than Q_5, which Appendix B explicitly permits. The source's arithmetic Artin convention and positive cyclotomic weight are translated into the manuscript's negative Tate weight. The same change is made to both modular and r_5 weights. All embeddings give the same integer exponent because the local base is Q_5.

7. **Local/integral conditions.** No crystalline hypothesis or bound on an integral lattice is used. The local character need only be de Rham. Finite inertia at five means an open unit kernel after the exact cyclotomic correction; finite inertia away from five follows from continuity and the finite coefficient field. No quantitative conductor bound is asserted at this stage.

8. **Exceptional cases.** Weight one is excluded by the nonzero weight gap. Negative or zero cyclotomic powers are allowed before the comparison; the equations force zero. The real sign is finite. Ramified primes of eta are permitted and absorbed in the finite modulus. No class-number-one assertion for another number field or global unramified-character argument in the function-field setting is used.

9. **Downstream consumer.** V13 lines 843–850 then absorb the finite Dirichlet character, take the primitive weight-two newform, and proceed to the Li/Shimura constituent identification. Those source applications are separate. The later conductor calculation concerns the final representation/newform, so this review does not assert that an intermediate twist preserves the original form's level. V13 lines 7248–7259 use a distinct determinant-based route; that argument was separately reviewed in the Pan packet and is not offered as a substitute for the actual earlier citation. None of these facts alone completes the height estimate or the 318/326 arithmetic witnesses.

## History, present incorporation and scope

I read the actual retained A011 argument in `parallel-galois-height-report.md`, not only its status. It already gave the finite-coefficient Hom-line, Q_5-only local algebraicity, all-prime inertia and ray-class argument. The present check independently restores the original source, reconciles the source sign convention explicitly, corroborates the cited Tate result in a published book, and binds the actual V13 consumer. It is not a newly invented repair to an already justified argument.

The exact V11 early consumer, companion route and bibliography all occur uniquely and byte-identically in V13; their old/new ranges and hashes are in the manifest. The current archived audited baseline also contains the exact early twist paragraph. This current incorporation check is separate from the older report's whole-manuscript approval scope.

No blocking defect was found in this bounded application. The actual r_5 construction and geometric/de Rham sources, Pan's theorem, the standard modular representation and its weights, finite twisting/newform existence, Li/Shimura and the remaining height/witness construction retain their own review obligations. This report is a source/application review deliverable, not a blanket independent approval or a new formal Lean theorem.
