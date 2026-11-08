# Independent V13 conductor-to-primitive-level review

## Decision

**ACCEPT this bounded application, relative to the named upstream construction of the modular compatible system.** The published Carayol and Casselman statements apply to the actual primitive weight-two form and prove CL1–CL2: its minimal level exponent equals the conductor of the full local representation. The application covers the prime 5 by the transported 3-adic realization, and covers all other primes, including 2 and 3, with the 5-adic realization. It retains arbitrary nebentypus, wild conductor and nonzero monodromy.

No new source-availability or application mismatch was found in this seam. This is not acceptance of Pan’s primary JAMS publication comparison, the geometric producer, numerical ramification estimates, Li/Shimura Jacobian realization, the height theorem, the whole restricted converse, or literal-318 sourceArithmetic. No source theorem was independently reproved and no Lean compile was run.

Active target: manuscripts/quartic_v13.tex, SHA256 9db71bbfcefb37db56eabcf40a5f9dd85de9ed58294635da3dbf6d4f5caa8fcd. The reviewer did not author the target text. BINDINGS.json pins nine construction, comparison, application and downstream passages. Their historical V11 counterparts are byte-identical; the target of this decision is V13.

## Primary evidence and version status

Both original published journal scans were freshly retrieved, hashed, rendered and read at the actual statement pages. The hashes match the retained source pins exactly:

- Carayol, Ann. Sci. ENS 19 (1986), 409–468: d4a5fb6b1cd76f944f8948e06df1c7ad5656ae5ee14b9189178ee1e8f2b0dab8. The primary archive is NUMDAM. Printed pp.409–411, including 0.2–0.7 and Theorems A/B, were visually inspected.
- Casselman, Math. Ann. 201 (1973), 301–314: 7f91ebae1a8f5e695800f4afb9fc06d0e2ea0b3a476751a31a7c8c3f38ad537d. The Göttingen published scan was retrieved from a CNRS mathematics mirror; its journal heading, institutional catalog and author’s publication list agree. Printed pp.301–302, 306–307, 309 and 313 were visually inspected.

Carayol’s initial download timed out, but the resumed transfer completed and verified against the full known hash. That temporary transfer failure is resolved, not a remaining evidence gap. The PDFs, rendered images and extracted third-party text are private research evidence and are excluded from the distributable archive.

A bounded correction search checked the actual titles and author/publication records. No relevant correction was found. Casselman’s author-page warning about a major correction belongs to his 1974 admissible-representation notes, not the 1973 newforms paper. Search results mentioning other authors’ errata were not attached to these sources. No exhaustive absence-of-corrections claim is made.

The retained A032 acceptance concerns the theta/U_p application. It is useful source history, but it does not by itself establish this distinct conductor/height consumer. This review binds the latter directly.

## The actual object entering the source theorems

V13 first constructs the scalar-corrected action rho_l=b(sigma)^-1 a_sigma mu_sigma composed with sigma. The B-action and chosen matrix units split it as two copies of the two-dimensional r_l. These same representations, not representations of an auxiliary family, are used throughout.

Pan is used only at 5. After the separately justified finite character is absorbed, the manuscript selects the **primitive** weight-two form f and its level N. The representation Pi_f is unitary cuspidal, with arbitrary finite nebentypus of conductor dividing N. Its real type is D_(2,0), so Carayol’s weight and parity conditions hold. The base field Q has degree one. The additional finite discrete-series-place condition in Carayol 0.3 applies only to even degree, so it imposes no extra condition here.

Casselman’s local theorem concerns irreducible admissible infinite-dimensional GL2 representations, as supplied by the local factors of Pi_f. His global minimal-level statement is applied after passing to the primitive form, not to an arbitrarily enlarged oldform level. On Gamma0(N), ad is 1 modulo N; hence his classical character factor epsilon(a)^-1 equals epsilon(d), exactly the usual nebentypus convention. No trivial-character or squarefree-level restriction has been introduced.

## Why the same form controls the prime 5

The chosen coefficient field contains the finitely many algebraic normalization scalars and values of b, splits B, and is enlarged to contain f’s coefficients. At primes outside a finite bad set, the reduction of mu_sigma composed with relative Frobenius is a quasi-endomorphism of the good reduction of A. Its rational Tate characteristic polynomial is independent of the coefficient prime. After multiplication by b(sigma)^-1 a_sigma and division of the four-dimensional trace by two, the trace of r_l is one algebraic number in that coefficient field.

Equality with f’s trace at the chosen embedding into Qbar_5 is therefore equality of algebraic numbers, since that embedding is injective. Transport through an embedding into Qbar_3 gives equality of traces away from a finite set. Chebotarev and Brauer–Nesbitt identify the semisimplifications, and the already established absolute irreducibility of r_3 identifies the representation itself. No Pan theorem at 3 is needed. Excluding the finitely many primes dividing N from the comparison set is harmless and is explicit in the expanded baseline passage.

The same reasoning identifies the Carayol representation in the appropriate dual convention. The manuscript does not need the unpublished Ribet observation following Carayol’s Theorem A: a two-dimensional representation whose semisimplification is the known irreducible r_l cannot have a proper invariant subspace and is itself irreducible.

Consequently the prime partition is complete:

- At p=5 use coefficient characteristic 3.
- At p=2, p=3 and every other p different from 5, use coefficient characteristic 5.

Every use has p different from l. No local compatibility theorem in the equal-characteristic case p=l is being assumed.

## Full local conductor and conventions

Carayol’s Theorem A is the result used. The extraordinary dyadic exception appears in the intermediate Theorem B, not in A. The source supplies the full local Weil–Deligne parameter at the relevant places; it is not merely an identity of good-prime Euler factors. Its Frobenius-semisimple parameter still contains the monodromy operator N.

The passage between Carayol’s geometric-Frobenius/cohomological convention and the Tate convention involves duality and an unramified norm twist. Neither changes the conductor. One can check this directly from the Weil–Deligne formula

a(r,N) = a(r) + dim(V^I) − dim((ker N)^I).

An unramified twist leaves the inertia representation and the kernel term unchanged. For the dual, finite inertia has exact invariants in characteristic zero; dimensions of invariants and the rank of the induced monodromy map are preserved. The Swan term is preserved as well. Extending the coefficient field changes none of these dimensions. This is why no conductor exponent is lost when matching the same modular representation in the Tate convention.

As a check against a common mistaken substitution, an unramified two-dimensional special parameter with rank-one N has conductor 0+2−1=1. Discarding N would incorrectly give zero. The manuscript explicitly forbids that substitution. It also retains the Swan term, which matters at dyadic and other wild places.

Casselman’s conductor-zero additive character is compatible with using the same additive character in Carayol’s epsilon-factor equality. The exponent then gives the same local conductor. Changing the additive character would shift both epsilon exponents by the common dimension-dependent term; it is unnecessary here. Equality of the full local parameter together with the minimal-newform statement proves

a_p(r_l) = a(Pi_f,p) = v_p(N), for p different from l.

## Actual consumer and remaining boundaries

The result is exactly CL2 at V13 lines 7342–7362. It converts bounds on the constructed r_l into bounds on every prime exponent of the **same primitive level N**. That is the level used in LR5, N≤210^300 R², and then in the modular-Jacobian height calculation LR6. Prime powers in N are allowed, so this is not merely a bound on its radical.

The local ramification estimates feeding LR5 are separate mathematical claims. This review does not reprove them. Likewise, the identification of a Tate constituent inside J1(N), its geometric source, the isogeny/height arguments and the final RC/318 assembly remain separately owned. Their actual downstream passages are pinned to prevent a generic conductor statement from being mistaken for completion of those tasks.

APPLICATION.json contains all nine required/constructed/why-match/evidence obligations. The accepted source interface is present, the constructed object is identified, the coefficient-prime coverage is complete, and the normalizations preserve the exact local conductor required by the consumer.
