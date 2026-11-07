# Javanpeykar sign and normalization review

## Finding and scope

PASS at the stated source-application scope. The three reviewed cusp-to-Jacobian modules use the correct arithmetic-degree sign, minimal-model inequality direction, factorial-normalized Wronskian, tensor weight, complex-embedding average, and positive Faltings-height shift. The direct finite-divisor argument removes the covering degree without reversing an inequality. The actual differential, Wronskian, finite-place and final Jacobian bounds are derived in the Lean composition; the underlying arithmetic surface, modular model and Arakelov identifications remain explicitly named geometric inputs.

This review does not assert a Lean construction of an arithmetic surface, its dualizing sheaf, global holomorphic differentials, or the whole `FiveContact49Height` proposition. It does not turn the three explicit Arakelov hypotheses into proved geometric facts. No changes were made to the reviewed sources or repository.

## Primary evidence

Ariyan Javanpeykar, *Polynomial bounds for Arakelov invariants of Belyi curves*, arXiv:1403.6404v1, 25 March 2014, with appendix by Peter Bruin. The exact PDF is `five-contact-metric/javanpeykar-2014.pdf`; its SHA256 is recorded in `receipt.json`. Printed pages equal PDF pages for the cited material. The source was inspected as extracted text and the key formulas on pages 10, 11, 23, 24 and 28 were visually checked against rendered original pages. The rendered images are retained in this review directory.

Secondary normalization cross-check: Gaudron–Rémond (2014), printed pages 351–352, exact PDF `isogeny-height-transfer/gaudron-remond-2014.pdf`. Its original-versus-shifted height distinction agrees with Javanpeykar Lemma 2.4.4. The 2022 isogeny theorem's original-height convention is not silently identified with the shifted convention; downstream monotonicity is a separate bridge.

## 1. Differential energy and Wronskian normalization

On printed page 5, the Hermitian pairing is `(i/2) integral omega wedge conjugate(eta)`. In a holomorphic embedded coordinate z=x+iy with omega=f(z) dz, `(i/2) omega wedge conjugate(omega)=|f(z)|^2 dx dy`. Therefore a globally norm-one differential has ordinary local area energy at most one on the embedded disc. There is no factor two and no genus divisor in this individual energy. The distinct canonical probability measure uses the sum divided by g; substituting that measure for ordinary area would be a mistake, but the reviewed Lean interface does not do so.

Printed page 6 defines the Wronskian matrix with entries `f_k^(l-1)/(l-1)!`. Its tensor weight is `k=g(g+1)/2`. This agrees exactly with `WronskianFinite318.wronskian`, indexed by `Fin g`, and the actual area estimate proved in `ActualWronskian318`. A unitary basis change may alter the local scalar by a unit-modulus determinant; its norm, which is the quantity used here, is invariant. Coordinate changes produce the weight-k differential, not an extra factorial constant.

The local analytic packet starts with actual holomorphic functions and actual area integrals. Supplying them as coordinate expressions of the global orthonormal basis remains an explicit geometric interpretation; the scalar estimate by itself does not construct such a basis.

## 2. All complex embeddings, with no additional one-half

Printed pages 7–9 sum over every embedding `sigma:K -> C`, not only one representative of a nonreal conjugate pair. The degree of a metrized line is its finite contribution minus the sum of `log ||s||_sigma`. The global Wronskian norm is the geometric mean with exponent `1/[K:Q]`.

Thus `avg f=(sum_sigma f(sigma))/[K:Q]` is exact. A pair of conjugate embeddings occurs twice on both sides, as it should. No additional factor one-half belongs in the formula. `CuspArakelovData318.embeddingAverage` uses the actual finite type `(K ->+* C)` and the theorem `NumberField.Embeddings.card`; it does not assume the cardinality or silently replace the sum by a sum over places.

## 3. Stable minimal height is bounded above by chosen-model height

Lemma 2.3.1, printed pages 9–10, states

`h(b) <= (Q, omega_Y)/[K:Q]`

for any regular model Y of the same curve. The proof factors the map to the minimal regular model into blowups, with `omega_Y=phi^*omega_X + E`; the section contribution of E is nonnegative. The chosen-model height increases under blowup. The correct input is an inequality, not equality.

In the proof of Theorem 4.5.1 on printed page 28, the divisor is the divisor of the rational differential `d(pi)`. It explicitly gives

`h(b) <= F_b - avg log ||d(pi)||_Ar`.

This is exactly the direction and minus sign of `minimal_model` in `SourceJacobianBound318.jacobian_GR_bound`.

## 4. Non-Weierstrass point and the exact cancellation

Theorem 2.4.1, printed page 10, states, for a non-Weierstrass b,

`h_Fal(X) <= k h(b) + log ||Wr||_Ar(b)`, with `k=g(g+1)/2`.

There is no extra R(X), Green-function, or additive genus constant in this theorem. The proof already absorbs those identities into the actual Wronskian norm.

At each embedding choose one and the same local coordinate q in both occurrences. Put

- a_sigma = log |d(pi)/dq|;
- m_sigma = log ||dq||_Ar;
- w_sigma = log |Wr_q|.

Then `log ||d(pi)||=a_sigma+m_sigma` and `log ||Wr||=w_sigma+k*m_sigma`. Consequently the two published inequalities give

`h_Fal <= k F_b - k avg a_sigma + avg w_sigma`.

The m terms cancel exactly. Multiplication by k preserves the first inequality because k is nonnegative. Coordinates may differ between embeddings; each embedding must use the same coordinate in both identities. The reviewed code uses one common `metricLog` function and precisely this coefficient k.

The whole selected fiber must avoid Weierstrass points to justify the theorem at every conjugate. `Data.nonWeierstrass` visibly requires nonvanishing of the actual factorial Wronskian. The actual derivative is nonzero from the cusp derivative estimate, alternatively from avoiding the branch values. The cotangent metric is positive on a nonzero coordinate differential. These nonzero conditions justify the geometric logarithmic norm identities. Lean's total convention `log 0=0` cannot itself replace the non-Weierstrass hypothesis; the packet does not claim that it does.

## 5. Direct finite-divisor domination

Let Y be the normalization of the finite cover of `X=P1_(O_L)`, let Y' be its minimal resolution, and f:Y'->X. Use the actual relative canonical divisor `K=div(d(pi))`. Put

`D_bound=[0]+[1]+[infinity]+2 sum_(p|6N) m_p div_X(p)`,

where `m_p=floor(log d/log p)`.

At nonexceptional horizontal components, the different coefficient is e-1<=e; the base canonical coefficient -2 at infinity can only help. At nonexceptional vertical components, Lemma 4.2.3 on printed page 24 gives `r<=2 e m_p e_p`, exactly the coefficient of the pullback of the indicated rational-prime divisor. Here `div_X(p)` includes the ramification multiplicities above p. The source's local-degree argument uses local degree at most d; it does not need local degree to divide d. The model theorem's separate vertical support excludes branch primes p>d, where m_p=0, and the separate modular good-reduction input restricts support to p|6N.

Set `Z=f^*D_bound-K`. It is effective outside the exceptional locus. For each exceptional component E, `Z.E=-K.E<=0`: the pullback intersects a contracted curve trivially, while minimality plus adjunction gives K.E>=0, the same input used in Lemma 4.2.1 on printed page 23.

If Z has a nonzero negative part N, then N is exceptional. Write Z=Z_+-N with disjoint effective supports. For E in the support of N, `N.E>=Z_+.E>=0`; the final inequality follows from nonnegative intersection of distinct effective curves. Hence N.N>=0, contradicting negative definiteness of the exceptional matrix. Thus Z is effective. This argument works directly on the regular resolution and does not assume the different divisor on the singular normalization is Cartier.

The selected section is not contained in the support of Z, because its generic point lies above a value outside {0,1,infinity}. Therefore intersecting Z with the section preserves nonnegativity. In the projection formula the map from this section to its base section has degree one, so no factor d is introduced. The normalized intersection of `div_X(p)` with the section is log p: all ramification and residue degrees sum to [L:Q]. This yields

`F_b <= horizontalContact(a) + 2 sum_(p|6N) m_p log p`.

For the actual a=1/n with n=2^128+i>=2, the elementary horizontal contact is at most `3 h(a)`. This agrees with the positive rational p/q calculation on printed page 28. The restriction a in (0,1) matters: the same 3h statement for an arbitrary rational is not justified without an additional constant. The reviewed `reciprocal_horizontal_bound` uses exactly 1/n and n>=2, so this is not a gap in the present application.

The matrix and normalized section-weight fields in `FiniteData` represent precisely these geometric inputs. Its derived `intersection` is the canonical finite contribution, and the Lean negativity proof derives the domination rather than receiving the final finite-height inequality as a premise. Constructing the actual model and proving that its matrices and weights satisfy the fields remain explicit upstream geometry.

## 6. Original and shifted stable Faltings heights

Javanpeykar Lemma 2.4.4, printed page 11, explicitly states that the Bost/Gaudron–Rémond convention used there is larger:

`h_plus=h_Fal+g log(sqrt(pi))`.

The sign is positive. The same relation is confirmed by the squared Hodge-norm definitions in GR2014, printed pages 351–352. The reviewed `GR_normalization` has exactly this direction. Since log(sqrt(pi))<1, replacing the shift by +g is safe for g>=0 and is included before the quadratic-log budget.

The 2022 Gaudron–Rémond Theorem 1.9 states its degree bound in the original convention. Using the larger h_plus in a monotone maximum enlarges that bound, which is valid, but it is not equality of conventions. The separate normalization ledger and downstream Lean monotonicity bridge preserve this distinction. Equal-dimensional isogeny variation is unchanged by the additive shift.

## 7. Exact status of the reviewed glue

The snapshots reviewed here are `CuspArakelovData318`, `SourceFiniteDivisor318`, and `SourceJacobianBound318`. Their hashes and the source PDF hashes are recorded in the receipt. A copied strict-kernel replay and recursive allowed-axiom audit accompany this report.

The resulting bound `h_plus(J_H)<=2^11 d^2 log(6dN)^2` is a theorem from:

1. actual cusp functions, actual holomorphic differential-coordinate functions and ordinary area energy bounds;
2. the actual finite intersection data with negative definiteness, local different domination, adjunction and section pullback formula;
3. the two named Arakelov inequalities and the named height-normalization identity.

The geometric production of these data, the arithmetic modular-cover/model interpretation, and the connection to the entire five-contact family are not proved merely by this numerical/analytic glue. The `FiveContact49Height` boundary must remain visible until those producers are supplied at the agreed proof level.
