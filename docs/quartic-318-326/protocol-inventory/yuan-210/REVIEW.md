# Yuan's theorem at the actual discriminant-210 consumer

Date: 2026-11-08. Reviewer: /root/restart_group_law. This is a bounded source/application and dependency review, not a new geometric construction, compiler replay, or approval of the entire height theorem. No shared repository files changed.

## Decision

Accept the actual classical application of Yuan's Theorem 1.1 to the maximal discriminant-210 stack and its **same universal fiber**, with the retained antecedents listed below. The source gives the required integral image 210·ω² and the exact metric isometry; the producer uses the correct maximal model over Z, not a nonmaximal-level statement over Z[1/3]. The positive log210 and logπ corrections, and the absence of a level-degree factor, match the literal consumer.

The existing FIBER-PRODUCER, MAXIMAL-KS-PRODUCER, METRIC-PRODUCER and independent metric reviews contain substantive classical object/map comparisons. The absence of a Lean construction of those objects is not evidence that this classical argument is missing. Nevertheless the actual Lean constructor of MetricSections and the global RefinedGeometricRealization is still absent, so neither unconditional FiveContact49Height nor unconditional literal318/326 soundness is certified here.

One generality error in the inspected English source is recorded below: its scheme-smallness sentence says 'contains U(N)' where that cannot be a sufficient condition for arbitrary U. The actual principal-level-three application uses U=U(3) and an independent torsion-free marking argument, so it does not require the false larger-U inference.

## 1. Exact source/version and read boundary

Xinyi Yuan, *Explicit Kodaira–Spencer map over Shimura Curves*, English translation dated 30 April 2024, https://faculty.bicmr.pku.edu.cn/~yxy/preprints/explicit_KS.pdf, SHA256 ad751f65ac5730b437adbabba78cc6bc1fe1f2249367c74566fe0a495100740e.

The retained author publication page explicitly identifies this linked PDF as the English translation of the published Chinese article in Acta Mathematica Sinica, Chinese Series 67(2)(2024), 227–249, DOI10.12386/A20220154. Its exact cached page is bound in manifest.json. The current V13 bibliography says exactly that. I verified the cached source hashes and freshly read the source; no new retrieval or exhausted final-source search was repeated. The original Chinese body was not independently compared. This is therefore an author-attested translation application, not a claim of fresh final-Chinese-text equivalence. The earlier bounded correction search found no article-specific correction; it is retained as such and is not represented as a new exhaustive search.

Fresh read scope: pp.1–6, especially the definitions, metrics and Theorem1.1; pp.10–13 through the reduction of the integral-image proof to local good/bad-prime calculations. Printed pp.3 and6 were also visually inspected. The detailed proof of the whole theorem, its deformation-theory predecessors, and its entire bad-prime calculation are not re-proved or independently audited here. The published theorem is the external input.

## 2. Required source datum versus actual producer

Yuan fixes an indefinite rational quaternion algebra B, a maximal order O, an open level U⊂Ohat*, and n(U), the product of primes where U is not maximal. His stack over Z[1/n] parametrizes actual relative-dimension-two abelian schemes A with O-action satisfying det(β|Lie A)=Nrd(β), plus the specified level structure. For μ∈O with μ²=−d_B, the compatible principal polarization is automatic. The stack is regular, flat and semistable, smooth away from d_B, and proper for division B.

The actual producer takes the indefinite **division** algebra of discriminant210, its maximal order O, and μ0²=−210. The retained embedding argument uses the nonsplitting of Q(√−210) at all four finite ramified primes and conjugacy of maximal orders in the indefinite rational case. It is a construction for this O, not a choice of an unrelated isogenous surface. The determinant condition is the one defining the actual PEL moduli problem; it is unchanged by forgetting a level marking.

For the height identity Umax=Ohat*, so n=1. The relevant maximal stack M and universal abelian scheme exist over Z. The fine principal-three model has U=U(3), n=3, and is used over Z[1/210] for controlled fields and tame ramification. These two bases are not conflated.

The substantive FIBER-PRODUCER identifies the generic X210 and its W quotient from the actual González–Rotger quotients, then uses the quaternionic PEL moduli datum and the whole canonical adelic model. Its level scheme retains all geometric components. The 36 effective markings and the 16 Atkin–Lehner elements give the actual 576-element fiber torsor. None of those counts, the canonical action, or the contact-coordinate identification is a conclusion of Yuan's KS theorem. They are retained geometric predecessors, read here to check the identity of the object to which Yuan is applied.

### Smallness sentence in the translation

The text on pp.5–6 says the quotient is a curve/scheme if U 'contains U(N)' for N≥3. Read as a condition on arbitrary U, this is too weak: the maximal group also contains principal congruence groups and still has central stabilizers. A sufficiently small subgroup should be contained in such a principal subgroup. This observation is about the inspected English wording only; I have not checked the Chinese wording or an author-issued correction.

The actual use does not infer a scheme for an arbitrary larger U. It takes the principal group U(3) itself. In addition, a polarized O-linear automorphism fixing a full three-marking has finite order and acts on the integral Tate module in 1+3M4(Z3), a torsion-free group. Hence it is identity, so the actual full-three moduli problem has no automorphism stabilizer. The retained producer supplies this argument and the actual marking, including at the ramified quaternion prime three. The maximal model is correctly retained as a stack throughout. This local wording problem does not alter Theorem1.1's stack-level image or its application here.

## 3. The comparison is literally the same surface

For the actual selected fiber (A,i,η) over the controlled field L, the morphism of moduli problems is

(A,i,η) ↦ (A,i).

Forgetting η does not replace A by an isogenous variety. By the universal property, pulling the maximal stack's universal surface back to this point gives A with its actual O-action, identity section and compatible polarization. Invariant differentials commute with this base change. Thus the source Hodge determinant λ at this point is det H0(A,Ω1), not the Hodge line of a guessed surface sharing a coarse coordinate.

After a finite auxiliary field extension K, properness gives an integral object Spec O_K→M. The universal abelian scheme computes the stable Hodge height. This auxiliary field is allowed to be larger than the controlled field used in the separate degree576 or isogeny estimates; no estimate silently substitutes [K:Q] for the bounded field degree. Stable normalized height is unchanged by the extension.

The canonical line evaluated is the pullback of ω_M². It is not replaced by ω_Y² of an integral level cover. Pullback of a fixed line to an actual point has no factor36,576, or ramification divisor. Such divisors would arise only after substituting the relative dualizing line of the cover, which the producer explicitly does not do. Nor is a point height the global intersection number of a finite cover.

The coarse generic curve has no elliptic stabilizers beyond ±1: the discriminant210 elliptic corrections vanish (5 splits in Q(i), 7 splits in Q(√−3)). The central involution acts trivially on the base differential and on the determinant of the two invariant differentials. Thus the generic canonical sections pulled from X210 are the appropriate rational sections on M. No division by two from integration on a stack is inserted into evaluation at an actual object.

## 4. The exact KS map, all primes, and the norms

Theorem1.1 applies to the canonical determinant KS map ψ3 obtained by the successive maps on pp.2–3, including the actual compatible principal polarization. It gives

ψ3: λ² → ω_M²,     image(ψ3)=210·ω_M²,

as an integral injective morphism, with the indicated induced Petersson metric equal to the tensor-square Faltings metric. This is stronger than a rational isomorphism of line bundles and is exactly why the finite-prime term can be retained.

Pullback along Spec O_K remains injective: locally this is multiplication by210 up to a unit, and210 is a nonzerodivisor in every O_K. No claim is made that arbitrary characteristic-p base change preserves this injection. At p=2,3,5,7 the image is still the actual sublattice210ω²; those primes have not been inverted on the maximal stack. At infinity, Yuan's norm is ||dτ||Pet=2Im τ and his squared surface Hodge norm is (2π)^−2 times the integral.

For a metrized line M with induced sublattice210M, normalized degree satisfies

h(210M)=h(M)−log210.

Thus

h(ω_M²)=2hYuan(A)+log210
       =2hOriginal(A)+2logπ+log210.

The second equality uses the original dimension-two L2 squared norm (1/4) times the integral. Yuan's norm is smaller by π^−1, so its degree is larger by logπ. These are pointwise normalized arithmetic degrees, not the global intersection formula in Theorem2.2, whose factor one-half serves a different expression.

The actual section producer uses t=32s, finite branch values0,32,76832,−343 and the fifth value infinity, and q0=(dt)²/P(t), q1=tq0. The retained metric proof verifies horizontal regularity, vertical extension of J²qi with J=2765952000 on the actual regular semistable stack, and the archimedean bound J²·4Cmet. Yuan's norm contributes the factor four for quadratic differentials. These section proofs are independent predecessors to the theorem application, not consequences of its scalar degree identity. They were read here, but this record does not repeat their full curvature or codimension-two proof review.

## 5. Exact translation into the literal record

MetricSections stores a canonical FrameNorms and a Hodge FrameNorms, with equality

InducedLattice318.induced canonical 210 = InducedLattice318.square hodge.

This is an equality of **all** finite and infinite frame norms, not just their summed degrees. The definitions match the geometric image: induced retains the infinite norm and divides each finite gauge by |210|. To see the frames explicitly, choose any nonzero rational Hodge frame e over K and choose the canonical generic frame g=ψ3(e²). No global integral generator of either line is required. At infinity, ψ3 gives ||g||=||e||². At every finite place, its isomorphism onto210ω² gives gauge_ω²(g)/|210|=gauge_λ(e)². These are exactly the two components of ks_image in these matched frames.

Write the actual evaluated J²q0,J²q1 as a0g,a1g. At an admissible finite s=u/v, q0 is nonzero and q1=32(u/v)q0, so a0≠0 and the exact stored ratio holds. The integral and supremum section estimates give finite_integral and arch_bound. The Hodge frame's normalized degree is the actual shifted surface height. This explains the classical construction-to-record correspondence; it is not a claim that a Lean term realizing these objects has already been supplied.

InducedLattice318.ks_degree derives canonical.normalizedDegree=2hYuan+log210 from that all-place equality. MetricSections.original_bound then yields the strict original-normalized +120 estimate, while shifted_bound uses logπ≥0 for the larger shifted estimate. CMInputs.toLegacy passes surfaceHeight+logπ; NonCMInputs.toLegacy uses its already shifted surfaceHeight. These branches preserve, rather than conflate, their conventions.

The global RefinedGeometricRealization quantifies over every coprime u,v with all five primitive contact forms nonzero. It requires actual CM/non-CM arithmetic producer data and the metric record over an auxiliary number field. Its declaration explicitly does not assert existence. The final source_soundness, polynomial318_soundness and stored326_soundness each still take this hypothesis. No new compilation or axiom audit is claimed by this read-only source check.

## 6. Nine application obligations

1. Source hypotheses: indefinite division B210, maximal O, determinant condition, μ0 and its actual compatible polarization, Umax for KS. Matched relative to the retained actual PEL producer.
2. Constructed objects: same universal fiber A after forgetting level, its determinant Hodge line and the maximal-stack dualizing square. Not an abstract equal-height or isogenous substitute.
3. Domain/index coverage: all admissible primitive pairs, all canonical components, all number-field places. Maximal model covers the ramified primes; the whole level model supplies the initial points. The formal universal constructor remains open.
4. Transition maps: actual level-forgetting moduli morphism, universal-family base change, canonical determinant KS map, ordinary line pullback. No replacement by a level-cover canonical line.
5. Object identity: the evaluated Hodge determinant belongs to the same A used in the arithmetic producer. The contact sections are actual tensors on that maximal model. No inverse limit is involved.
6. Coefficients/normalization: image210, induced finite gauges, tensor-square norms, positive log210, positive logπ, norm2Imτ and quadratic factor4. No global-cover degree or stack factor enters point height.
7. Local conditions: integral extension at every place after allowed auxiliary extension;210 remains a nonzerodivisor; bad-prime image is not erased; finite sections and archimedean bounds are retained actual-model proofs.
8. Exceptions: do not apply a nonmaximal Z[1/3] result at inverted primes; do not infer arbitrary characteristic-p injection; do not use the English text's larger-U smallness sentence; do not conflate auxiliary and controlled fields.
9. Downstream consumption: exact MetricSections fields, then ks_degree/original_bound/shifted_bound and conditional refined soundness. This is neither the entire non-CM/CM arithmetic producer nor unconditional49/8.

## Remaining boundaries and reuse

The result is a bounded acceptance of this classical source application, with exact hashes in manifest.json. The author-attested translation limitation is unchanged. González–Rotger quotient identification, Deligne canonical action, PEL and proper-stack extension inputs, section/curvature proof, and original-height convention are retained with their actual reports, not silently reaudited from foundations. Their separate formal realizations and the full RefinedGeometricRealization constructor remain required. Missing Lean data must not be relabeled as a newly discovered absence of classical justification.

No third-party PDF, extract or rendering is public in this packet; only the authored review, manifest and binding metadata are allowlisted.
