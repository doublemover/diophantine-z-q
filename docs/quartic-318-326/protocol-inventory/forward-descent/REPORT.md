# V13 forward rank, finite Kummer descent, and the actual pole consumer

Review date: 2026-11-08. Author/reviewer: model worker `/root/restart_contact_field`; model identifier is not exposed in this runtime. This is a bounded primary-source and argument review, not a Lean replay or an independent acceptance of this newly assembled application record. No shared manuscript, branch, or proof source was changed. Whole-file and excerpt bindings are in `APPLICATION.json`; source versions, hashes, read pages, and retrieval failures are in `sources.json`.

## Active Version 13 binding

The current target is Version 13, SHA-256 `9db71bbfcefb37db56eabcf40a5f9dd85de9ed58294635da3dbf6d4f5caa8fcd`. Version 11 is the historical origin of the retained proof and repair, not the active baseline. I independently found and byte-compared all eight relevant inherited body/bibliography passages in the actual V13 file. The current corank/forward lemmas are at 1157–1194, simultaneous realization at 7787–7890, parity completeness at 7892–7940, and preparation-zero at 10563–10635. Bibliography locations were found separately, not guessed by adding seven: they move by 1840 lines. `version-comparison.json` gives every exact range and hash.

The V12/V13 additions explicitly build different 498/514 and 394/411 reductions on inherited inputs. They do not replace this contribution's literal 318/326 source or alter its ordered Kummer coordinates and pole maps. I checked the whole-version delta classification, their retained-input introductions, and that no duplicate labels or command redefinitions change these inherited references. This is dependency-scope comparison, not approval of those new reduction proofs. The following V11 locators are historical and map to the active V13 spans in the application record. The current consumer-document snapshot is bound at the observed repository head; the separate V13 documentation amendment is reviewed independently.

## Result

The actual forward inference needed by the two-twist construction is mathematically supported: once the manuscript supplies its computed two-Selmer dimension three and its restricted converse for each actual curve, the published rank-one theorem and finite Kummer sequence produce rational points in the prescribed extra class, with nonzero abscissa. The intermediate Cassels–Tate argument uses the finite quotient by the maximal divisible subgroup, not an incorrectly asserted nondegenerate pairing on its two-torsion.

A substantive source-version improvement is available without changing the theorem: the manuscript's MPI/90-69 text has a published counterpart in Kolyvagin's ICM Kyoto proceedings article, published by the Mathematical Society of Japan in 1991, pp. 429–436. I read the official IMU scan and compared its Theorems 1–5 with the cited preprint. Theorem 1 on printed p. 430 says analytic rank at most one gives the same Mordell–Weil rank and finite full Sha. The inequality was visually checked, because OCR incorrectly renders it as strict. The exact publication binding proposed here still needs a non-author review and incorporation; the manuscript currently cites the preprint and its old page numbers.

Coverage remains incomplete for the final-published-version comparison of BCDT: the AMS PDF returned HTTP 403, while the Harvard deposit and the two author versions inspected/located have placeholder journal metadata. This is a source-coverage limitation, not a mathematical counterexample to modularity. The historical audit explicitly recorded the same limit; it must not be silently upgraded. The full proof of RC, the entire prime-selection/local descent producer, and the all-288-row witness construction are not certified by this review. The finite class-to-point and pole-coordinate maps below are checked at their actual objects.

## 1. Exact external inputs and versions

### Kolyvagin: the actual published forward theorem

V. A. Kolyvagin, *On the Mordell–Weil Group and the Shafarevich–Tate Group of Modular Elliptic Curves*, Proceedings of the International Congress of Mathematicians, Kyoto 1990, vol. I, Mathematical Society of Japan, Tokyo, 1991, pp. 429–436. The official IMU volume is preserved locally; its PDF pages 517–524 are extracted without changing page content into `primary/kolyvagin-published-429-436.pdf`.

The hypothesis on p. 430 is an actual modular elliptic curve E/Q with a weak Weil parametrization X_0(N) → E, N its conductor. Theorem 1 on that page covers analytic ranks zero and one and asserts finite **full** Sha, with no good-ordinary condition, residual irreducibility hypothesis, or exclusion of 2. Rational two-torsion is allowed. This is not merely a theorem about a prime-to-2 quotient.

The proof route on p. 431 is explicit. Choose a negative fundamental discriminant D, a square modulo 4N, D unequal to −3 and −4, with gcd(D,2N)=1. Theorem 4 supplies infinitely many such D with analytic rank one over K=Q(sqrt(D)); for a rank-one base it attributes the nonvanishing theorem to Waldspurger. The rank-zero branch instead uses Bump–Friedberg–Hoffstein/Murty–Murty. Theorem 3, attributed to Gross–Zagier, identifies a simple zero over K with a nontorsion Heegner point. Theorem 5 gives rank one and finite Sha over K. Equation (3), σ(eP_D)=−ε(eP_D), makes the free line invariant in the analytic-rank-one case. Restriction on Sha has kernel killed by [K:Q]=2, contained in the finite group Sha(E/Q)[2]. Finite kernel and finite target imply finite full Sha over Q, including its 2-primary part.

The same published article, p. 432 equations (4)–(5), states the finite Kummer sequence and the Selmer definition by **all** local Kummer images, together with finiteness of the finite-level Selmer group. This directly supplies the cohomological exactness consumed below. Its Section 2 removes auxiliary restrictions on (M,λ) arising from torsion in an earlier construction; no odd-M restriction is added to the stated theorem or Kummer sequence.

The preprint and publication have the same numbered forward statements and connecting proof at the inspected locations, but their bytes and pagination differ. This is a statement/proof-passage comparison, not a claim that the entire files are identical. Targeted title/author/erratum searches found no relevant correction to these statements. That limited negative search is not a guarantee that no correction exists.

### Gross–Zagier: what is actually used

B. Gross and D. Zagier, *Heegner points and derivatives of L-series*, Inventiones Mathematicae **84** (1986), 225–320, DOI 10.1007/BF01388809. The author-hosted file is a scan of the published article with the actual publisher header; the author's bibliography happens to print volume 85, but the article itself says 84. The manuscript's volume 84 is correct.

Read I.3 p. 227, I.6 pp. 230–231, and the proof/comparison in V.1 pp. 306–308. Theorem I.6.3 identifies the derivative with a nonzero positive scalar times the canonical height of the actual f-component of the class-group sum of the Heegner divisor. The hypotheses are an odd negative fundamental discriminant coprime to N, D square modulo 4N, the weight-two newform at level N, and the specified class-group character. Kolyvagin's auxiliary D satisfies these hypotheses, including splitting at every bad prime. The relevant class-group character is trivial. The finite quotient/isogeny to the actual elliptic curve preserves non-torsion; it does not identify integral Tate lattices.

Theorem I.7.3 on p. 231 also directly states that a modular elliptic curve with a simple central zero has a rational point of infinite order. It **does not** supply rank exactly one or finite Sha, so it cannot by itself replace Kolyvagin in the class-to-point argument. No numerical Gross–Zagier period or height constant is used here, only nonvanishing. The published paper explicitly corrects its earlier announcement's height-base factors in I.6.4, and the old-form ambiguity in the choice of Heegner point on p. 307. These are harmless for this nonvanishing use; no incorrectly normalized equality is imported. Targeted searches and the author's publication page disclosed no additional correction affecting this use; that is the extent of the errata search.

### Poonen–Stoll and the actual correction

B. Poonen and M. Stoll, *The Cassels–Tate pairing on polarized abelian varieties*, Annals of Mathematics 150 (1999), 1109–1149, DOI 10.2307/121064. I compared the published EMIS scan (Trinity mirror), the author's version dated November 6, 1998 with minor correction August 23, 2014, and the author's current errata list.

The exact input is the nondegenerate alternating pairing on Sha(E)/Sha(E)_div for an elliptic curve over a number field: published pp. 1109–1110. Section 6, Corollary 7 and Theorem 8, pp. 1122–1123, explain the square-order/two-torsion consequence. The rational origin supplies the rational divisor inducing the principal polarization. General principally polarized abelian varieties can have only antisymmetric pairings at 2; no such generalization is used here.

The erratum on PDF p. 3 corrects the assertion that every infinitely divisible element lies in the maximal divisible subgroup without further hypotheses. Equality holds if M[p] is finite for every prime p. Finite-level Selmer finiteness and the Kummer sequence give this condition for Sha, so the correction does not invalidate this application. The author's current Section 2 includes the extra hypothesis explicitly. The errata entry on PDF p. 6 concerns a later positive solution to the finite-field surface Brauer-group question in Section 11; it has no role in these elliptic curves over Q.

No nondegeneracy of the pairing restricted to F[2] is asserted or needed. A finite 2-group with a nondegenerate alternating pairing decomposes into paired cyclic factors: choose an element of maximal order, pair it perfectly with another element of the same order, split off the resulting hyperbolic pair, and induct. Consequently dim_F2 F[2] is even.

### BCDT and the exact modularity-to-target seam

The literal V11 citation is BCDT, *On the modularity of elliptic curves over Q: wild 3-adic exercises*, author manuscript, Theorem A and Introduction conditions (1)–(6), published JAMS 14 (2001), 843–939, DOI 10.1090/S0894-0347-01-00370-8. The inspected Harvard copy contains the author article rather than final publisher pagination. Theorem A covers every elliptic curve over Q. The six equivalent definitions identify the same elliptic L-series, the conductor-level weight-two form, and an actual Q-morphism X_1(N(E)) → E. Intermediate lifting hypotheses do not become hypotheses on Theorem A.

Kolyvagin formulates modularity using X_0(N) → the actual E. The historical report supplies the conductor-level rational newform, quotient q_f:J_0(N)→A_f, Q-isogeny α:A_f→E, and π(x)=α q_f([x]−[∞]). This is the exact comparison required; X_1(N) → E alone should not be relabeled X_0(N) → E without this step. The report cites Milne's 2017 notes for the quotient construction; those are exposition, not a newly checked primary publication. This review records that remaining source/definition seam explicitly rather than claiming that a finite isogeny is an isomorphism or that integral lattices coincide.

## 2. The finite descent inference, on the actual E_l

Fix l>0 squarefree, l≡11 mod12, and E_l:y²=x(x−l)(x+3l). Its discriminant is 2304 l^6 ≠0. Its rational 2-torsion consists of O,(0,0),(l,0),(−3l,0). Neither modularity nor the published forward theorem needs l to be prime, or the representation on E_l[2] to be irreducible.

Assume the specific manuscript computation dim_F2 Sel_2(E_l)=3. Since E_l(Q) is finitely generated, dim E_l(Q)/2E_l(Q)=rank E_l(Q)+2, even if other torsion is present. Finite Kummer exactness therefore gives r+dim Sha(E_l)[2]=1. The 2-primary group is cofinitely generated: its finite 2-torsion bounds the number of generators of its compact Pontryagin dual, so it has the form (Q_2/Z_2)^t ⊕ F with F finite. The pairing gives dim F[2] even. Thus r+t+dim F[2]=1 forces F=0 and r+t=1. The full 2-primary Selmer corank is one; this is not yet rank one or finite full Sha.

Now apply **the manuscript's RC** to this same l, then Kolyvagin's published forward theorem. RC supplies analytic rank one; the forward theorem supplies algebraic rank one and finite full Sha. Reapply the finite Kummer dimension identity: 3=(1+2)+dim Sha[2], hence Sha[2]=0. It would be invalid to derive Sha[2]=0 merely from finite Sha. In fact this dimension inference already follows from rank one and the computed dimension; finite full Sha is additional output.

Kummer exactness is now a surjection E_l(Q)/2E_l(Q)→Sel_2(E_l), so the **specified** class (β,1), not an arbitrary nonzero class or an isogenous curve's class, is represented by a point on E_l(Q).

## 3. Coordinates, local coverage, torsion, and two simultaneous twists

The manuscript uses the ordered Kummer coordinates (x+3l,x−l), not (x,x−l). Away from 2-torsion their squareclasses are obtained from the functions having divisors 2(−3l,0)−2O and 2(l,0)−2O, respectively. These are the standard coordinate realization of the finite Kummer map; their specific coordinate comparison is an internal connecting argument, not a theorem numbered in the Kolyvagin article. The full local matrix computation in V11 is an internal proof and is not attributed to a newly invented external '2-descent theorem'. Its general local-image facts are substantive inputs to inventory if a complete source audit is claimed.

The four torsion images, with the limiting values at roots rather than division by zero, are
- O: (1,1);
- (l,0): (l,1);
- (−3l,0): (3,−l);
- (0,0): (3l,−l).
For example the vanishing coordinate at x=l is replaced by l(4l)=4l²; at x=−3l it is replaced by (−3l)(−4l)=12l². Thus the formulas agree with the exact ordered coordinates.

In the simultaneous construction β>0 is squarefree and β≡17 mod24, so β is not a rational square. The support of l is B_0∪I∪{q_0}, or this union together with J=supp θ. Since q_0 is fresh, β/l is not square. Since l>0, −l is not square. Consequently (β,1) is different from every displayed torsion image on **both** curves. A point representing it is not O or any root point, so x,y,x−l,x+3l are nonzero. The cubic then gives [x]=[(x+3l)(x−l)]=β in Q×/Q×². This is the needed nonzero abscissa squareclass, not just existence of some nontorsion point.

The manuscript constructs both supports at once before RC is invoked. β and θ are positive squarefree, disjoint, prime to 6, β≡17 mod24, θ≡1 mod24, with mutual local squareness. Its fresh primes give n squarefree, coprime to 6θ and n≡11 mod12; nθ satisfies the same RC congruence. θ=1 is allowed, and the same point can then be reused. The rank theorem is applied pointwise to each actual conductor, not uniformly in l or to one chosen isogeny class for the family.

The precise local requirements in V11 are:
- all odd good primes: the unramified/even-valuation Kummer subgroup;
- p|l, p≠2,3: the two torsion images have independent valuation vectors and span the local image;
- at 3: the first coordinate is unrestricted and the second is square; l≡−1 mod3 makes the torsion images supply the unit and uniformizer generators;
- at 2: both coordinate valuations must be even; if both differences have valuation one, substitution gives an impossible square congruent to l mod8. If both are divisible by 4, their difference 4l and the cubic force both valuations even. The actual extra class is trivial locally since β≡1 mod8, so merely necessary dyadic parity equations are not used as a sufficiency argument;
- at infinity: first coordinate positive and positive second coordinate subgroup of index two. The actual (β,1) is trivial there.
At p|θ, β is square by the stated mutual-square hypothesis. At p|β and the fresh support primes, the particular class is matched to a torsion class using K1_B0=0. At 3, β and l have the same nonsquare unit class. These are exactly the local conditions whose assembled producer is needed. This report checks their role and the small-prime/zero seams; it does not claim a new independent reconstruction of every CRT, reciprocity, matrix, and local-image proof in the producer.

## 4. Exact map to the preparation-zero pole

There is already a full internal V11 theorem and proof at lines 10556–10628, label `v5:preparation-zero-bridge`. It is not merely an assumed unpublished Brox theorem. `PREPARATION-ZERO.md` records this separate locator without changing the earlier frozen downstream trace.

For its completeness direction, b>0 has square reduced denominator, is square in Q_2,Q_3,Q_17, and satisfies b<17, v_2(b)≥3, v_3(b)≥1, v_17(b)≥2. Put B=17b and V=B²(1−b/17)>0. The proof constructs the required β/θ pair and applies the simultaneous lemma. Write V=θc² with c≠0. Scale the second point (x,y)↦(c²x,c³y), taking E_(nθ) to E_(nV). If the first abscissa is Ba², a≠0, divide both curve parameters by a² and both point coordinates by a²,a³. The resulting curves are E_e0 and E_(e0V), and the abscissas are B and Bs², s≠0. Set e=e0/B, p=y1/B, q=y2/(B²s), h=e(B−b²). Since e0V=B²h, direct substitution gives
p²=B(1−e)(1+3e), and Bq²=(s²−B h)(s²+3B h).
All denominators used to choose the witnesses are nonzero. No extra nonzero guards on e,p,q,s,h are imposed on the polynomial's arbitrary solutions. The earlier parity lemma also allows U=0, giving θ=1. The theorem excludes b=0; the separately checked finite normalized-conic equivalence has its own explicit b=0 branch. Those different domains must not be conflated.

The old component's e equals B times the V11 e; p,s,q are unchanged. The subsequent ThreeHelper normalization is the already checked finite algebraic map with old e=b·e_new, old s=b·s_new, old q=b·q_new, and p unchanged. These are separate substitutions with different meanings of e; the B·h factor in V11's second conic is essential. The exact finite joins and final scalar's local arithmetic are bound in the earlier immutable receipt, not reclassified as missing deep arithmetic here.

## 5. Consumer strength and unresolved work

The actual final arithmetic target remains
`∀ z : ℤ, CircuitReplay.HasSolution (Raw318FinalReplay.stage0 (Current318FinalPolynomial.scale : ℚ)) (z : ℚ)`.
It requires one compatible assignment satisfying all 288 source rows. For the final scalar a=114444r and b=a(W/(1+a))², the earlier finite-join addendum proves the necessary elementary inequalities and local square conditions **if** the same chosen W satisfies the required positivity and unit conditions. This review supplies no such simultaneous common W, no prime-ray/guard/anchor choice, and no complete assignment. The canonical 326 lift is already a finite input-preserving construction and introduces no new arithmetic premise.

Decisions are therefore separated:
1. Accepted within this bounded non-author reading of the existing mathematics: the finite Selmer/corank inference, the post-RC rank-to-prescribed-point inference, and the exact point-to-pole substitutions, relative to their explicitly retained producers.
2. Newly assembled publication binding: Kolyvagin ICM and Poonen–Stoll correction evidence are ready for non-author review and incorporation; no manuscript edit or self-acceptance is claimed.
3. Incomplete source coverage: BCDT final published text/corrections and the authoritative X_0 actual-target quotient comparison have not been fully newly validated. General coordinate/full-local-image descent facts and the full simultaneous producer need their own complete source/proof coverage before global closure.
4. Unchanged arithmetic obligations: full RC, simultaneous all-row witness production, and any uniform/effective strengthening remain open. No Jacobian/PEL, height, or unrelated geometric expansion was resumed.

Historical classification: prior justification was found in V11 and the earlier forward-modularity report, with the preprint/publication and BCDT version limits explicitly retained. The existing preparation-zero proof is an internal argument already present in V11. The new work improves source binding and makes the consuming maps explicit; it is not evidence that every earlier reviewer checked them.
