# Independent conductor, primitive-contact, and level-normalization review

## Outcome and precise scope

The source's modular level calculation is sound at its stated mathematical application scope. The normalizer/fiber construction, the integral tame quotient argument, the controlled sign lift, and the two compatible coefficient primes give

- a normal fiber field of degree dividing 576;
- an auxiliary normal field of degree at most 2304 R;
- a primitive weight-two newform of level N, with rad(N) dividing R and N at most 210^300 R^2;
- nebentypus kernel index at most 4608 R, independent of the degree of its coefficient field.

Here R can be the **actual fixed fifteen-prime product times the actual finite odd-contact radical** used in ContactRadical318, not only the historical product of every prime below 76176. The exact primitive detector coordinates are (2a+b:a), for t=a/b in reduced form. No change to 49/8 is licensed by the old exponent-24 theorem: the newer metric-cancellation/isogeny argument must still be supplied separately.

This is an independent mathematical proof/application audit of the indicated upstream constructions and conventions, not a Lean construction of Shimura curves, Galois representations, or their conductors. The accompanying NebentypusOrder318 module kernel-checks the actual group-theoretic determinant/order/index step. The end-to-end source theorem continues to take FiveContact49Height as an explicit argument until the entire geometric height producer is assembled.

## 1. Inputs checked and what they establish

The source passages are quartic_v10.tex 6847–7400 and 8920–9030, and the adopted arithmetic.md sections finite-exceptional-primes and height-49-over-8. The generic quotient/fiber realization is independently reconstructed in fiber-field-bridge/FIBER-PRODUCER.md. Its actual model is the maximal-order quaternionic Shimura curve of discriminant 210, with the whole principal-level-three cover, not one selected component. Its quotient has the five rational branch values infinity, 0, 1, 2401, -343/32, each of inertia order two. Its effective normalizer group has order 576. The same packet's group/Galois proof shows that the normal splitting field of the complete fiber has degree dividing 576, rather than merely at most 576 factorial.

Fresh primary checks in this review:

- Pan, arXiv:1901.07166v2, Conjecture1.0.1 and Theorem1.0.4, printed2 and5. At coefficient prime5 the regular irreducible odd potentially semistable representation is modular up to twist; the extra condition in the theorem belongs only to prime3. No residual-image assumption is being silently imposed at5.
- Silverberg–Zarhin, AIF45 (1995), printed405–406, Definition3.1 and Theorems3.2–3.5. Full rational11-torsion supplies semistability in residue characteristics2,3,5,7; potential good reduction then makes it good. The stated theorem is not applied at residue characteristic11.
- Casselman, Math. Ann.201 (1973), original printed302,306–307,313, visually checked. The local minimal central-character eigenspace defines the conductor; the epsilon-factor exponent agrees. The global minimal level is the product of these local conductors, including nontrivial nebentypus.
- Carayol, Ann. ENS19 (1986), original printed409–411, visually checked. TheoremA supplies full local Weil–Deligne compatibility at every place unequal to the coefficient characteristic, including2. The extra finite discrete-series-place hypothesis is only for even-degree totally real fields, hence absent over Q. Duality and the unramified normalization twist preserve the conductor.
- Yuan, Explicit Kodaira–Spencer map over Shimura Curves, 30 April2024 author translation, §2.1, printed5, and introduction printed2–4. The actual maximal model is regular, proper, semistable, and smooth away from the quaternion discriminant; the sufficiently small level cover is fine and carries the universal abelian scheme. Metric normalization is separately reviewed by the metric worker.

This audit does not claim that the author versions and published versions of Pan or Yuan are byte-identical. Exact versions and inspected files are recorded in the receipt. The standard different/ramification formulas below are used at mathematical theorem scope; they have not been imported as Lean local-field theorems here.

## 2. Integral model and exact support R

The following independently reconstructs the integral step; the definitive model realization is coordinated with FIBER-PRODUCER.md.

Work over Z[1/210]. The effective level-change group has order36, invertible on this base. Its generic action is free. For a finite tame group acting on a smooth relative curve, the fixed locus of a subgroup is smooth over the base: after an etale localization, average a lift of a relative parameter to diagonalize the stabilizer action. A special fixed point therefore lifts to the generic fiber. Thus a generically free effective level action has no new special fixed points, and the fine level cover of the coarse maximal curve is finite etale.

The Atkin–Lehner action extends to the smooth stable model. Specialization is faithful for this tame finite group. A stabilizer of a geometric smooth-curve point injects into its tangent-line units and is cyclic. Since W has exponent2, nontrivial stabilizers have order2. The fixed locus of an involution is finite etale: locally its nontrivial eigenvalue is -1, and the averaged parameter z=(u-sigma(u))/2 satisfies sigma(z)=-z. The derivative+1 alternative would give the identity, contrary to faithful specialization. Distinct involution fixed loci cannot meet, since their joint stabilizer would not be cyclic. Hence precisely the five generic branch sections persist, with no extra vertical branch outside210. Three disjoint rational sections canonically identify the smooth genus-zero quotient with P1 over the base.

Take a prime p not dividing210. Over the strict henselization of Z_p, a branch chart is w=z^2, up to a unit that has a square root there; away from the branch sections the cover is etale. If a rational section has finite even contact m=2k, then w=p^(2k)*u with u a unit. Its root p^k*sqrt(u) lies in an unramified algebraic extension. Every further principal-level lift is etale, so every point of the complete fiber is unramified. This argument also treats infinity, with local parameter v/u instead of u/v. Because the normal field is the kernel field of the action on all fiber points, trivial inertia on all points means the entire normal field is unramified.

The principal-level scheme is proper over Z[1/210]. The valuative criterion extends each L-point at every place above p not dividing210; its universal abelian scheme extends too. Thus the actual surface has good reduction at those places, even when the fiber field is ramified. Good reduction is not inferred merely from the numerical branch determinants.

For primitive integers (u,v), min(v_p(u),v_p(v))=0. The primitive forms are

v, u, u-v, u-2401v, 32u+343v.

Outside2 the last one has exactly the contact valuation with -343/32. Every nonzero pairwise determinant has support in {2,3,5,7}. Consequently, outside210, at most one form has positive valuation. Absence from the odd-contact radical means that this unique positive contact, if any, is even. The preceding local calculation therefore proves that ramification of L, and bad reduction of the surface, are supported in210 times this radical.

The adopted bad set is {2,3,5,7,11,13,17,37,41,73,109,359,439,2399,4801}; it contains all primes of210, as well as every auxiliary prime explicitly excluded later. Thus R=badProduct*radical has exactly the needed support. No step above needs an upper cutoff76176. Merely replacing B* by the smaller product inside the historical numerical height inequality would be invalid; rebuilding its geometric support as above is what permits this replacement.

## 3. Exact primitive detector and scalar coordinates

Write the actual detector t=a/b with gcd(a,b)=1 and b>0. The linear map (a,b) -> (u,v)=(2a+b,a) has determinant-1, so (u,v) is primitive. Its five primitive forms become

a, 2a+b, a+b, b-2399a, 407a+32b.

These are precisely the source root factors after multiplying by the reduced denominator and the respective unit coefficients 1,2,1,-2399,407. DetectorContactMap318.form_identity checks this identity, and member_raw_contact checks the exact positive-odd rational valuation conversion, including denominator integrality. ContactHeight318.detector_primitive and detector_height_loss check the primitive map and h(t)<=h(u:v)+log3. A contact polynomial nonzero forces every form nonzero. In particular no prohibited projective point has been fed to the height theorem. The separate t=1 zero-height lemma does not assert a nonexistent quotient constraint.

For scalar beta the coordinates are instead (beta.num:beta.den), with no detector Mobius change. Its square form forces even numerator and denominator valuations at every good prime, so zero and infinity contacts disappear. The scalar packet checks the remaining three contacts against the literal four-factor r, including the additional root1/2 and its collision primes359 and4801. It invokes the genuine p^8 index theorem. The beta=0 branch is handled by height0, not by the omitted-contact geometric theorem.

## 4. Potential good reduction and the torsion extension

A semistable reduction of a surface with its division-quaternion action cannot have a positive-rank torus. Restricting the extended endomorphisms to the maximal torus gives a unital map B -> M_t(Q), 1<=t<=2. Simplicity makes it injective. Dimension rules out t=1; t=2 would identify a division algebra with a matrix algebra. Hence the semistable reduction is good. This uses extension to the Neron model and preservation of its maximal affine subgroup, not injectivity of specialization of every arbitrary endomorphism ring.

Let E=L(A[11]). The actual normalizer isogeny between any conjugate fiber and A may be chosen of degree prime to11: at11 the maximal-order normalizer is Q_11^*GL2(Z_11), so rescale rationally to an11-adic unit and clear other denominators by an integer prime to11. All geometric Hom maps are L-defined by the full-three-torsion argument supplied separately. Thus conjugate11-torsion kernels coincide; E/Q is normal. Its degree is at most576*|GL4(F11)|<2^66.

At residue2,3,5,7, full11-torsion plus the checked Raynaud criterion gives semistability over E; the quaternion argument makes it good. The prime11 does not use this torsion criterion. It is treated later by the p>7 tame argument. The exact integer degree comparison is reproduced by check_constants.py.

## 5. Controlled scalar splitting, without bounded coefficient degree

B-compatible conjugate isogenies have scalar discrepancies c in Q*. Multiplying each by the positive fourth root of its reciprocal degree normalizes their discrepancy to a sign cocycle epsilon. This cocycle is inflated from Gal(L/Q). Its local Brauer class is zero outside the ramification support T.

For every odd place with nontrivial sign invariant choose an odd Dirichlet character modulo p; at2 use the odd character modulo4 when required. Their product chi is tame at odd primes and has local conductor at most4 at2. Its order m is at most2*product_(p in T,p odd)(p-1), hence at most2R.

For constant root-of-unity coefficients, the obstruction to a character square root on a local multiplicative group is its value at-1. The valuation and principal-unit free factors admit character square roots; the finite torsion factor gives exactly this obstruction. This identifies the local boundary of chi with the sign class. Brauer reciprocity and the local-global injection identify them globally, giving a continuous cochain b with b^2=chi and delta b=epsilon, valued in mu_(2m). This claim concerns only the sign cochain; the full splitting also contains the positive degree-normalization scalars.

On G_L, b is a conjugation-invariant character. At a prime outside T its inertia restriction is quadratic. A quadratic rational twist, ramified at exactly the finitely many such odd primes and possibly2, kills those restrictions. It changes neither b^2 nor delta b and does not enlarge its value group. The kernel field L' is normal and [L':Q]<=2m[L:Q]<=2304R. This construction does not bound the coefficient field independently of R.

## 6. Modularity and the coefficient-prime switch

The normalized action b(sigma)^(-1)*a_sigma*mu_sigma*sigma commutes with B. After splitting B it is r_ell direct-sum r_ell. On G_L' it is the actual Tate action of A. Faltings semisimplicity and the exact geometric endomorphism algebra B give absolute irreducibility of the multiplicity representation. Proper-smooth comparison and finite descent give weights{0,-1} and potential semistability. Complex conjugation followed by the holomorphic isogeny exchanges the two Hodge summands, so the two-dimensional multiplicity action is nonscalar; its corrected square is1, hence determinant-1. It is unramified outside T and ell.

Pan's precise prime5 theorem therefore applies. Comparing Hodge–Tate weights with the modular weights forces weight2 and a weight-zero twist. On G_L', (det r5)^2=cyclotomic^2. The quotient determinant/cyclotomic thus has finite image globally. Comparing with the modular determinant makes the square of the twisting character finite, and the character itself finite. Absorb it into the form and take its primitive newform, with arbitrary nebentypus.

For p outside T and {3,5}, the quasi-endomorphism obtained by composing the reduced isogeny with relative p-Frobenius has a characteristic polynomial independent of the Tate prime. Its half-trace, with the fixed algebraic scalars, supplies compatible traces for r3 and r5. Equality at5 is an equality of algebraic numbers, and transports to3. Chebotarev and semisimplicity then identify r3 with the realization of the **same** primitive form. Thus r3 computes the conductor at5 and r5 computes it at every other prime. No p=ell local-global compatibility assertion is needed.

## 7. Exact primitive level and Artin conductor

Casselman's minimal-level theorem, including its central-character eigenspace, gives v_p(N)=a(Pi_p). His original epsilon-factor statement uses an additive character of conductor zero. Carayol TheoremA identifies the full local Weil–Deligne representation at p different from ell. Its contragredient and unramified norm normalization do not change conductor. This includes any monodromy contribution, though potential good reduction in this application also forces finite inertia. It would not be valid to discard monodromy by semisimplifying only the inertia action.

Consequently v_p(N)=a_p(r_ell) for each p with a chosen ell different from p. The prime5 switch just proved supplies the missing case. No trivial-nebentypus, squarefree-level, or extra discrete-series-place assumption is used. The unpublished irreducibility remark after Carayol TheoremA is unnecessary: the constructed representation is already irreducible, and matching its semisimplification forces the original one to be irreducible.

## 8. Wild ramification and the numerical conductor budget

Put F=E Q(chi), where Q(chi) is the character's kernel field, not its field of values. Over F the cochain b is a conjugation-invariant quadratic character, so its kernel F' is normal over Q with [F':F]<=2. For p=3,5,7 the additions E->F->F' are tame, so v_p(e_F')<=65. At2 the character modulo4 and the final quadratic extension each add at most a factor2, giving v_2(e_F')<=67.

For a finite Galois local extension with ramification index e and different exponent delta, an Eisenstein uniformizer polynomial over the maximal unramified subfield gives

delta <= e-1+e*v_p(e).

Indeed the nonzero derivative terms have distinct valuations modulo e; their minimum cannot exceed the leading term's valuation. The upper-numbering different formula then gives

integral_(u>0)(1-1/|G^u|)du <= v_p(e).

Up to the last positive ramification break b, the nonzero integrand is at least1/2. Therefore b<=2*v_p(e)<=134. The manuscript uses the looser136. A two-dimensional representation trivial above136 has Swan conductor at most272, with tame term at most2, hence conductor at most274<300. This deliberately loose bound is safe even with an arbitrarily large tame ramification index.

For p>7, the fiber extension is tame because its degree divides576. The actual surface is good over L. On wild inertia the sign cochain's square is tame and the remaining image has order at most2; since wild inertia is pro-p, the cochain is trivial there. Thus the conductor is at most2. Outside T it is zero. Multiplying the exact primitive conductor exponents yields N<=210^300 R^2 and rad(N)|R. In particular the prime11 argument is tame and does not invoke11-adic torsion semistability at residue11.

## 9. Nebentypus and the improved index exponent

For the final primitive form, det r=epsilon*cyclotomic in the Tate convention. Squaring on G_L' shows epsilon^2=1 there. If q:G_Q->Gal(L'/Q), then q(g^d')=1 for d'=|Gal(L'/Q)|. Hence epsilon(g)^(2d')=1 for every g.

NebentypusOrder318 proves this for an actual homomorphism to any commutative group, and the exact order divisibility. For a field-valued character it further injects the image into the actual roots of X^(2d')-1, proving the **kernel index** is at most2d'. This distinction matters: character exponent alone does not bound image cardinality in an arbitrary commutative group. Its surjective-pullback theorem transfers the bound to the finite Dirichlet-character kernel. Thus t=[(Z/NZ)^*:ker epsilon]<=2d'<=4608R.

Weight2 gives epsilon(-1)=1. The actual degree of X_H->X(1) is therefore

d=N*t*product_(p|N)(1+1/p),

without a factor2 and without a cyclotomic coefficient-field factor. Since rad(N)|R, the primes p>=13 contribute at most R^(1/32); the product of the five possible smaller factors is1152/385<3. It follows that d<3*4608*C*R^(3+1/32)<2^14*C*R^(97/32). The height worker is separately kernel-checking this finite Nat.primeFactors/product step, rather than taking the index estimate as an unexplained scalar premise.

The CM branch must use the surface-height estimate854R followed by the geometric factor2 and additive120 (plus any explicit normalization shift). The frozen cm-surface-transfer packet supplies this corrected application. The older generic helper taking contact-height854R is not the direct source application.

The later equality 2*(97/32)+2*(1/32)=49/8 depends on the actual quadratic-log Jacobian bound, the Wronskian coefficient/embedded-disc argument, image-height transfer, and metric comparison. Those are separate producer lanes. Neither the conductor proof nor the old exponent-24 inequality establishes them by itself.

## Conclusion

No normalization or support defect was found in this audited chain. The exact bad-prime support, primitive detector coordinates, sign-field degree, compatible-prime switch, nebentypus index and full conductor are consistent. The primary-source applications and the actual tame integral-model argument remove the corresponding manuscript-level ambiguity; the remaining full FiveContact49Height formalization/assembly must still be reported as such. SourceHeightComparisons318.source_integer_input remains correctly conditional on that one geometric proposition.
