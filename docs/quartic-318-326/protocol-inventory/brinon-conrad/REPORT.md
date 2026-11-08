# V11 Brinon–Conrad application review

Reviewer: /root/restart_group_law. This is a distinct internal model review, not a human independent audit or a certificate of the whole height argument. No shared repository source has been edited.

## Result

No mathematical repair is required in the Brinon–Conrad portion of V11 Lemma `de-rham-descent`. The cited source actually proves the properties used: closure of de Rham representations under duals and subquotients, strict filtered compatibility, and invariance under a finite extension of the local base field. The manuscript's explicit finite Galois descent argument is valid. The actual consumer is the two-dimensional Tate multiplicity representation `r_ell`, and its coefficientwise Hodge–Tate weights are `{0,-1}`. At ell=5 this supplies the de Rham and distinct-weight input for the separate Berger/Pan steps.

This conclusion is conditional on the explicitly stated geometric comparison and actual double-copy restriction isomorphism. It does not newly certify the preceding scalar-corrected QM representation construction, Scholze comparison with its corrigendum, Milne's geometric duality, Berger's monodromy theorem, Pan's modularity theorem, or the complete 318/326 height and witness arguments.

## Source version and fresh inspection

The authoritative author-hosted file is Brinon and Conrad, *CMI Summer School Notes on p-adic Hodge Theory*, preliminary version dated June 24, 2009, https://math.stanford.edu/~conrad/papers/notes.pdf. A fresh download has 2,659,899 bytes and SHA-256 `f27d508bc64b3c9e2e9de5041429b2cb6a909b2cd72ff8096c20493f27b5a187`, exactly the prior project pin. It is not a published research article. V11's bibliography says so correctly.

The author's current webpage still describes these notes as undergoing revision and not in final form. A search of that page and the source version information did not identify a replacement published edition or a separate correction to the three consumed statements. This is a bounded version check, not proof that no relevant correction exists anywhere. The report does not silently upgrade the notes to a refereed publication.

I read the actual statements and proofs, not only prior verdicts: §5.1 and Example 5.1.3; Theorem 5.2.1 and its proof, printed pp.68–72; the filtration definitions and convention, p.76; Proposition 6.3.3 and its proof, pp.77–78; Proposition 6.3.8 and especially its finite-extension proof, pp.80–81. I visually checked rendered pp.68,77,80,81. These contain explicit proofs of the needed formal properties.

There is a harmless printed summation-direction slip in the proof of Proposition 6.3.3 on p.77: to obtain the dimension of the decreasing filtration Fil^i from graded pieces, the sum is over j >= i, not the printed j <= i. The already stated exactness of every graded sequence gives the displayed dimension equality with the corrected summation direction. No theorem hypothesis or conclusion changes, and this is not a manuscript gap.

## Actual V11 objects and applications

V11 lines 16465–16532 state and prove the relevant lemma. K/Q_ell and F/K are finite, A/F is an abelian surface, C_ell/Q_ell is a finite coefficient field, and r is a continuous two-dimensional C_ell-linear representation of G_K. The precise supplied isomorphism is

`V_ell(A) tensor_Q_ell C_ell ≅ r restricted to G_F ⊕ r restricted to G_F`.

The preceding representation construction occurs at lines 788–808 and 7207–7223: scalar correction makes rho_ell an actual G_Q representation commuting with the quaternion algebra; matrix units split it into two identical multiplicity summands, and its restriction to G_{L'} is the actual Tate action. Locally the lemma uses K=Q_ell and F=L'_v. This review checks the lemma's use of that exact isomorphism, not the earlier construction that supplies it.

The two consuming passages explicitly pass from de Rhamness to potential semistability using Berger, and then apply Pan at ell=5. The Tate convention assigns Q_ell(1) weight -1. The earlier twist argument at lines 828–835 separately cites Conrad's `locchar.pdf`; the companion argument at lines 7241–7252 uses a determinant and finite-image calculation. Neither is a citation to the Brinon–Conrad notes, and neither is silently certified by the present report.

## Nine obligations

1. **Required hypotheses.** Theorem 5.2.1 applies to a finite-dimensional F-linear representation and an (F,G)-regular period domain. Here the source's coefficient F is Q_ell, not the manuscript's local extension F. The period ring is B_dR, a field, with invariants equal to the local base; Example 5.1.3 explains its regularity. The representation under consideration is finite-dimensional over Q_ell after forgetting C_ell scalars. Proposition 6.3.3 is used only after de Rhamness is established. Proposition 6.3.8 is used only for a finite extension of complete local fields, within its stated domain.

2. **Constructed objects.** Start with the actual geometric H^1_et(A), whose de Rhamness is obtained from the separately cited proper-smooth comparison. Milne's canonical duality supplies the actual covariant Tate module. It is a dual, not a dual followed by an extra Tate twist. Theorem 5.2.1(3) transfers de Rhamness to the dual. Extending by a finite trivially acted-on coefficient field is, as a Q_ell representation, a finite direct sum. The displayed double-copy decomposition makes the underlying representation of r|G_F a direct summand of that de Rham representation.

3. **Required versus constructed domain.** All continuous finite-dimensional Q_ell representations needed here are covered. Both ell=5, used for modularity, and ell=3, used for the compatible-system conductor comparison, are allowed by this lemma; no residual-image restriction or odd-prime exception is inserted. The base extension may be ramified and need not initially be Galois. A finite Galois extension F'/K containing F is available. There is no Euler-system index set or omitted family of local primes in this application.

4. **Exact maps and their directions.** The dual and summand operations occur inside the given Galois representation, not through an arbitrary isomorphic rank-one object. For finite descent the map is the natural multiplication map

   `F' tensor_K (B_dR tensor_Q_ell W)^{G_K} → (B_dR tensor_Q_ell W)^{G_{F'}}`,

   where W is the underlying Q_ell representation of r. G_{F'} is normal in G_K and Gal(F'/K) acts semilinearly on the target; its invariants are exactly the source period module over K. Applying ordinary finite Galois descent to every filtration step proves the filtered isomorphism. The same period ring is used on both sides.

5. **Limiting or identity endpoint.** No new inverse limit is taken in the Brinon–Conrad step. The equality `dim_K D_K = dim_{F'} D_{F'} = dim_Q_ell W` establishes de Rhamness of the original W over K, not only a potentially de Rham replacement or a different representation. The earlier inverse limit from finite etale coefficients belongs to the separately named algebraic/rigid comparison. No claim about commuting arbitrary limits is smuggled into finite descent.

6. **Coefficients and conventions.** The de Rham functor here is the covariant invariant functor `(B_dR tensor V)^G`. The source's p.76 convention gives Q_p(n) weight -n. The de Rham H^1 of an abelian surface has graded dimensions 2,2 in degrees 0,1; duality gives Tate degrees 0,-1 with the same multiplicities. To make the coefficientwise assertion explicit, enlarge the finite local extension to contain a normal closure of C_ell and split its tensor product with C_ell by coefficient embeddings. In every factor the two isomorphic summands have the same graded multiplicities and together have dimensions 2,2. Each therefore has dimensions 1,1, giving exactly `{0,-1}`. This uses the double-copy isomorphism, not merely the dimension of r. Filtered descent preserves those multiplicities.

7. **Local and integral conditions.** This is a rational period-module statement. It gives no integral lattice, fixed conductor bound, or crystalline/semistable descent over K. It does not require good reduction over K: the input A/F is proper smooth as a variety, not assumed to have a smooth integral model. The manuscript correctly invokes Berger after descent to obtain potential semistability; it does not infer semistability itself by ramified descent.

8. **Exceptional cases.** Non-Galois F/K is handled by finite Galois closure. Ramification is allowed for de Rham descent. Coefficient embeddings are handled by the splitting argument above. Subquotients are used only inside an already admissible representation; closure under arbitrary extensions is not asserted. Hodge–Tate weights alone are not used to prove de Rhamness. The manuscript explicitly disclaims that incorrect shortcut at lines 16528–16532.

9. **Actual downstream consumer.** The conclusion applies to the same `r_ell` that was constructed from rho_ell, and in particular to `r_5` consumed by Berger/Pan at lines 808–826 and 7221–7239. This is one local hypothesis in the route to a weight-two modular form, a modular Jacobian factor and the later height estimate. The 318/326 active arithmetic document still treats modular realization and isogeny inputs as dependencies; its height49/8 derivation does not follow from this lemma alone. No current all-row witness or unconditional polynomial theorem is produced by this source check.

## Historical evidence versus current incorporation

I read the actual retained `parallel-a009-independent.md` report and the A009 application record. Its argument explicitly covers the filtered finite descent and coefficientwise multiplicity calculation, while leaving the construction of r_ell and its restriction decomposition as inputs. Those are the same scope boundaries used here.

I independently compared the current archived audited baseline `docs/theorem-application-audit/source/audited-baseline.tex` with V11: the entire lemma, proof and Hodge–Tate warning are byte-identical after selecting the exact shared block. The archive's whole-file hash is not the earlier report's pre-integration hash; the application register binds the current archive and records the subsequent anchor rebind. This report does not pretend the two whole manuscripts have identical hashes or that the historical review alone accepts every present consumer. The actual V11 applications were read anew and are bound in the manifest.

## Remaining boundaries

- No correction is needed to the reviewed Brinon–Conrad application.
- Upstream proper-smooth comparison, its corrigendum, the actual Tate duality and the actual QM/Morita representation are named predecessors, not newly discharged here.
- Berger and Pan, finite-twist removal, compatible-system conductor control, and the remaining height argument require their separate reviews.
- The preliminary notes remain an explicitly identified non-published source. The argument is not rejected merely for that status, nor is its status concealed.
- This report and manifest are a review deliverable, not the author's self-generated independent acceptance of a new application contract. A separate integrator/reviewer may adopt them at their exact hashes.
