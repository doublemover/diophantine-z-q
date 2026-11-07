# Actual cusp, finite-divisor and Jacobian-height assembly

## Checked result

`SourceJacobianBound318.jacobian_GR_bound` derives

h_GR(J_H) ≤ 2^11 d² log(6dN)².

`SourceNonCMHeight318.jacobian_49_over_8` and `nonCM_contact_49_over_8` then derive the adopted 49/8 Jacobian and non-CM contact bounds from the level/index and named image/isogeny/contact-metric producers. They do not take the final Jacobian-height bound as an assumption.

The four modules contain 12 public results. Strict kernel replay and all theorem axiom checks use only `propext`, `Classical.choice`, and `Quot.sound`. The exact finite/analytic objects in this assembly are actual Mathlib complex embeddings, q-parameters, derivatives, factorial Wronskians, Lebesgue disc energies, rational absolute heights, integer prime factorizations, and negative-definite intersection matrices.

This is not a construction of arithmetic surfaces, modular curves, Jacobians or their global Arakelov heights in Lean. The interpretation and existence of the explicit data below remain classical theorem/application inputs. Consequently it does not by itself construct a term of `ContactHeight318.FiveContact49Height` or erase that named hypothesis from the published source-soundness theorem.

## Archimedean data and normalization

`CuspArakelovData318.Data K g i N` records the source's coordinate data over **every** complex embedding σ:K→+*C. It includes the regular qj function, its holomorphy/outer majorant/constant term and selected value, actual width and upper-half-plane representative, and the actual coefficient functions of an orthonormal basis on the completed cusp disc. The energy field is ordinary Lebesgue area integral at most one. The actual Wronskian is required to be nonzero at the selected point, recording the non-Weierstrass input explicitly.

`actual_archimedean_bounds` consumes the frozen actual cusp theorem and frozen sharp local Wronskian theorem. It proves the averaged differential and Wronskian bounds. No differential-size, coefficient-size, Wronskian-size or radius bound is supplied separately. The average is the sum over all complex embeddings divided by [K:Q]. `NumberField.Embeddings.card` proves the constant-average normalization, so no missing or duplicate complex-pair factor is hidden.

The three global Arakelov inputs are named separately:

1. The minimal-model comparison and degree decomposition: pointHeight ≤ F − average(differentialLog + metricLog).
2. Javanpeykar's Faltings-Wronskian theorem: hFal ≤ k pointHeight + average(wronskianLog + k metricLog), k=g(g+1)/2.
3. The Gaudron-Rémond normalization: hGR=hFal+g log(sqrt(pi)).

The same metricLog at each embedding cancels exactly. It is not bounded. The result is converted into the actual log(6dN) budget, including the normalization shift, and only then into the 49/8 exponent.

## Finite data, including the selected-parameter restriction

`SourceJacobianBound318.FiniteData` records canonical and pullback coefficients on a finite family of exceptional and nonexceptional divisors, the actual exceptional intersection matrix and outside intersections, normalized section intersection weights, the local nonexceptional different bound, the adjunction intersection inequality, and the pullback/section projection formula.

The negative-definite matrix theorem proves canonical domination on the exceptional components. Nonnegative section weights then preserve the coefficient inequality. The horizontal term is the **actual valuation-weighted** `FiniteDivisorArithmetic318.horizontalContact` of 1/n. The exact source value is n=2^128+i, so n≥2 and 0<1/n<1. The no-constant horizontal bound is not asserted for arbitrary rational parameters: a negative parameter such as −1 would require an additional term.

The vertical term retains floor(log d/log p) and the actual prime set of 6N. The branch-prime-card estimate comes from the actual prime-factor product dividing 6N and 2^card ≤ that product. Thus it yields card ≤ log(6N)/log 2. Primes dividing 6N but exceeding d contribute zero floor terms; no artificial assumption that all prime divisors of 6N are at most d is imposed.

`canonical_section_bound` therefore derives the finite canonical intersection bound. It does not assume that bound as an input. The geometric input retained is the local different-coefficient theorem and actual interpretation of the matrix, section weights and pullback formula on the chosen regular model.

## Source/application evidence consumed

- `converse-work/cusp-producer`: complete source-specific cusp and whole non-Weierstrass fiber audit, nine kernel modules. Independent copied review: `cusp-producer-review`.
- `wronskian-local/frozen`: actual holomorphic-disc energy, sharp coefficient and factorial Wronskian estimates. The completed cusp is included, so holomorphic differentials have no missing center.
- `exceptional-negativity-bridge`: actual negative-definite matrix effectiveness theorem. Independently reviewed in `exceptional-negativity-review`.
- `finite-divisor-arithmetic`: actual horizontal valuation sum and vertical floor-log sum, with 0<a<1 retained.
- `finite-divisor-producer-review`: fresh Javanpeykar application check, printed pages 22–26 and 28. Local different bounds, minimal semistable resolution, negative-definiteness extension and degree-one section pullback give the exact model interpretation without a covering-degree factor.
- `modular-factor-producer`: actual Q-defined point-level X_H, rational j-map, Γ(N) and −I, exact SL2 degree, and actual non-CM surface image with g≥2. Its point/μ_N model convention is explicitly repaired by rational dual-isogeny transport and Fricke stability. No rational cusp assumption is needed here.
- `metric-cancellation` and `isogeny-height-transfer`: named global normalization/image/isogeny constants and exact scalar growth. These were previously source-audited; this packet replaces the formerly supplied final Jacobian bound with the actual cusp/divisor assembly.

The analytic worker independently reviewed the three core glue modules against the original Javanpeykar printed pages 5–7, 9–11, 23–24 and 28. It confirmed the minimal-model inequality direction, exact all-embedding average, differential sign, Wronskian weight and normalization. The final review ledger is kept separately and does not edit these sources.

## Formal boundary and use

To instantiate the result on the geometric objects, supply the source's modular qj/model data, restriction of normalized global differentials to the embedded discs, local different coefficients and regular-model intersections, and the three displayed global Arakelov identities. These are explicit objects and theorem applications, not a hidden whole-height assertion. The mathematical producer reports justify their source scope; they are not newly formalized algebraic-geometric constructions.

For a final all-contact theorem, the CM/non-CM dichotomy, actual contact-coordinate realization and corrected original/shifted height comparison are supplied by their separate packets. This assembly leaves those scopes visible and provides the new non-CM theorem they can consume.

Replay with `./verify.sh`. `receipt.json` binds sources, logs and all consumed packet receipts/primary-source reviews. No repository files were modified.
