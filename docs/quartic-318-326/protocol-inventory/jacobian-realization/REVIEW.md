# Independent V13 Li–Shimura–Faltings realization review

## Decision and scope

**ACCEPT the bounded source application, relative to the named upstream modular representation and geometric surface.** Li supplies the actual extra Fricke premise in Shimura’s theorem. Shimura gives a Q-defined quotient of J1(N). Its total good-prime Euler factors, together with Chebotarev and semisimple-character comparison, place the selected r5 in its Tate module. The common constituent over the existing Lprime then gives an actual Lprime-homomorphism and an Lprime-isogeny through Faltings and Poincare reducibility.

This is not an inference from equal traces alone. The exact bridge from traces to representations, and then from representations to geometric morphisms, is recorded below. The full QM/PEL source producer, Pan’s primary JAMS comparison, the separate J_H quotient producer, numerical height bounds and whole RC/318 conclusions remain outside this decision.

Active target: manuscripts/quartic_v13.tex, SHA256 9db71bbfcefb37db56eabcf40a5f9dd85de9ed58294635da3dbf6d4f5caa8fcd. Eight exact construction/application/consumer passages are pinned in BINDINGS.json. Their V11 counterparts are byte-identical, but this decision binds V13. The reviewer did not author the target passages. No shared repository edit, new proof expansion or Lean compile was performed.

## What was freshly checked

The four original published Li page scans (printed pp.285, 294, 296, 298), Shimura’s published JMSJ article, Faltings’s original 1983 article and the published 1984 erratum all freshly match their retained byte hashes. Actual statement pages were read visually; SOURCES.json gives every URL, hash and printed-page locator.

The Faltings erratum was not omitted. It replaces the preceding constant-height assertion in Satz 2 by eventual stationarity and explicitly says the corrected statement suffices for later results. It does not withdraw Satz 3 or Satz 4, the semisimplicity and endomorphism statements used here. No height estimate is inferred from the erroneous version.

A direct download of Milne AV v2.00 returned HTTP406. The official indexed source remained readable: Part I Proposition 10.1, p.42, and Part IV Lemma 3.9, p.143, were freshly read and the returned text is saved privately. Thus there is no missing statement here, but the whole Milne PDF bytes were **not** freshly verified. It remains an author course-note source, not a relabeled journal publication. The corrected-proof issue with I10.15 reported in the separate Milne audit is not consumed: the Hom theorem comes directly from corrected Faltings, while Poincare uses I Proposition 10.1 over a number field.

Bounded title/correction searches found no relevant Li or Shimura correction. This is not an exhaustive guarantee of absence. External PDFs, images and indexed source text are excluded from the distributable packet.

## 1. The exact Fricke condition

After its finite twist is absorbed, the manuscript has a normalized primitive weight-two newform f of level N and arbitrary nebentypus epsilon. Li’s definition allows such characters, including nonprimitive characters modulo N; only the necessary parity epsilon(−1)=1 is imposed at weight two.

Shimura’s Theorem 1 applies to groups between Gamma1(N) and Gamma0(N), including Gamma1(N). It constructs the quotient and coefficient conjugates without an extra Fricke assumption. Its final zeta-function assertion, however, requires either Gamma0(N) or stability of the full coefficient-conjugate span under

h(z) → h(−1/(Nz))/z².

The Gamma0 alternative cannot simply be substituted for the actual J1(N) application.

Li’s unnumbered paragraph immediately before Lemma 6 on printed p.296 is the relevant statement. With H_N=[[0,−1],[N,0]] and the determinant-normalized slash, each normalized newform satisfies f|H_N=gamma times its coefficient conjugate. The scalar is nonzero. The statement is not Lemma 6 itself, and does not require rational coefficients, trivial nebentypus or prime level.

Apply this to every coefficient conjugate. These conjugates remain primitive: Shimura’s unconditional conjugate-existence statement gives them at level N. If a conjugate arose from a primitive source at a smaller divisor level, conjugate that source back, use Li’s old/new decomposition, and apply Li’s Theorem 5 on p.298 to its good-prime eigenvalues. Equality of primitive forms forces the original level N, a contradiction. The induced character is restored by conjugating back. This argument does not use Shimura’s conditional zeta conclusion circularly.

Complex conjugation permutes the full set of coefficient embeddings, whether or not the coefficient field is Galois. Therefore the full complex span is stable under H_N. At weight two,

h(−1/(Nz))/z² = N(h|H_N)(z).

This is precisely Shimura’s required normalization. No claim that a single form is a Fricke eigenvector, or that gamma lies in its coefficient field, is needed.

## 2. A genuine quotient, then the selected Tate constituent

Shimura Theorem 1 gives q:J1(N)→A_f over Q, with connected kernel an abelian subvariety, dim A_f equal to the coefficient-field degree, and pullback differential space the full coefficient-conjugate span. Its zeta conclusion supplies the product of the corresponding modular degree-two Euler factors outside finitely many bad primes.

The next step is a representation theorem, not a purely formal reading of that product. Choose a finite coefficient extension containing all relevant embeddings of the coefficient field. Compare V5(A_f) after extension with the direct sum of the modular representations for all those embeddings, consistently in the Tate convention. Such modular realizations are the standard ones in the already audited Carayol/Pan interface. At common good primes the total characteristic polynomials, hence traces, agree.

Chebotarev density and continuity give equality of characters. For clarity, apply the characteristic-zero semisimple-character theorem to the finite-dimensional algebra generated by the two Galois actions; Milne IV Lemma 3.9 states this algebraic criterion explicitly. Faltings Satz 3 makes the Tate module semisimple, and characteristic-zero scalar extension preserves semisimplicity. One may compare with the semisimplification of the direct sum, so no separate unpublished irreducibility assertion about every conjugate modular realization is needed.

The particular embedding selected by Pan contributes the already known irreducible r5. It therefore occurs in V5(A_f). This argument compares the **whole direct sum** and then selects its known constituent. It does not pretend that a product polynomial by itself has labeled each separate coefficient factor.

Because q is an actual Q-defined quotient, its rational Tate map is surjective. Semisimplicity splits it, so r5 also occurs in V5(J1(N)). In the manuscript’s conventions r5 is the Tate constituent and r5 dual is the cohomological H1 constituent. Both the duality and the arithmetic/geometric Frobenius convention must be kept consistent; a coefficient field is not a field of definition for the abelian variety.

## 3. The same-field common constituent and geometric isogeny

The existing field Lprime is the kernel field of the scalar correction restricted to G_L. On G_Lprime the corrected four-dimensional action is the actual Tate action of A, so after splitting B,

V5(A) = r5 direct-sum r5.

The same r5 is present in J1(N). The representations of both abelian varieties over the number field Lprime are semisimple by Faltings. Thus their common constituent gives a nonzero G_Lprime-equivariant Hom after the finite coefficient extension.

This does not require enlarging Lprime. The invariant subspace in the finite-dimensional Hom vector space is the intersection of linear kernels (g−1); finitely many such equations already cut it out. Flat extension of coefficients therefore commutes with these invariants. Nonzero Hom after coefficient extension implies nonzero equivariant Hom over Q5.

Faltings’s published Satz 4 is stated for endomorphisms. Apply it to A×J1(N) over **Lprime** and take the off-diagonal matrix block. Its rational form identifies

Hom_Lprime(A,J1(N)) tensor Q5

with the corresponding equivariant rational Tate Hom. Thus the nonzero invariant Hom comes from a nonzero geometric morphism after taking a rational linear combination and clearing denominators. This is the named theorem that turns the representation statement into geometry.

Since A is absolutely simple, a nonzero A→J1(N) has finite kernel onto its image. Poincare reducibility supplies a complementary abelian subvariety Z over the same base field and hence an Lprime-isogeny A×Z→J1(N). The complement can be constructed as the connected kernel of the polarization map to the dual of the image. Everything is defined over Lprime; no bounded coefficient-field degree is needed. Milne I Proposition 10.1 provides this construction. Its imperfect-field qualification is irrelevant because Lprime has characteristic zero.

Consequently dim J1(N)≥2, as used by the height consumer. This proves existence of an isogeny only; it does not supply a numerical bound on its degree.

## 4. The later J_H consumer and boundaries

V13 also uses the character-kernel quotient J_H. Its separate preceding argument constructs A_f as a Q-isogeny factor of J_H by the diamond-invariant differential space and the effective quotient maps. **Given that actual quotient/factor construction**, the same Tate-constituent, coefficient-descent, Faltings and Poincare argument above applies with J_H in place of J1(N). The target passage and that explicit prerequisite are pinned; the quotient producer is not silently accepted by this review.

The actual consumers are the baseline transfer, the level-based transfer allowing unbounded coefficient degree, and this later character-kernel transfer. Their height, genus, Belyi and isogeny-degree inequalities are not consequences merely of Li, Shimura or Faltings’s Hom theorem and remain separate reviews.

APPLICATION.json records all nine required/constructed/why-match/evidence obligations. The retained A011 application and earlier independent Fricke work are preserved as review history; the current conclusion rests on fresh source checks and the exact active V13 consumers.
