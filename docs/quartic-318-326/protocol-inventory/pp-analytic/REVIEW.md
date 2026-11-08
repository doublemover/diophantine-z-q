# Prime-pattern and analytic source/application inventory

Date: 2026-11-08. Author: `/root/restart_modular_curve`.
Status: scoped source/application inventory and fresh Mitsui check; not independent acceptance of this packet, the complete PP theorem, or the final 318-variable theorem.

## Immediate findings

1. The complete Gaussian PP appendix is **byte-identical** in V10, V11, V12 and V13. Its 2,631 lines have SHA256 `e2cac3ab88ea581932cf596a8fbf19044241f18a621975c2b7ccfc7d0ef22d76`. Exact manuscript and excerpt bindings are in `revision-pp-bindings.json`. The V11 mathematical target remains V11; V13 does not silently replace it. The V11 Kato repair is a separate dependency and does not change the PP passage.
2. Mitsui's actual J-STAGE published PDF was freshly retrieved. It exactly matches the historical 2,823,723-byte SHA256 `b71fbd5ae9443991479a73a4e7bde68165b0c0e90b290cd0bd94fd9da416f963`. Printed pages 2, 11 and 12 were visually rechecked. The old fresh-retrieval gap is closed. This is not a claim to have independently re-proved Mitsui's entire paper.
3. Dodos–Kanellopoulos's final publisher record is verified: Acta Arithmetica 203 (2022), 251–270, DOI 10.4064/aa210728-27-2, published online 10 May 2022. Normal publisher download returned HTTP403. The author's public PDF was retrieved and its Theorem 5.1 checked: the required full-cyclic majorant norm is U^(2s), not U^s. This is an author manuscript and does **not** close final-typeset comparison. The old arXiv v4 source qualification remains.
4. Browning–Loughran's normal final AMS PDF URL returned HTTP403. The previously inspected accepted/arXiv Theorem 4.1 remains the evidence. Browning–Heath-Brown's previously inspected Oxford accepted manuscript is likewise not silently promoted to the final typeset publication. These are source-version coverage gaps, not counterexamples to the mathematics.
5. Existing analytic component reviews are preserved. There are two Mitsui application rows, thirteen norm/Type-I-II/factorization rows, and thirteen Gowers/transference rows in the retained inventories. Their source/interface and independent mathematical reviews have scoped upstream conditions. This report does not relabel them all as unreviewed merely because they are informal or not Lean.
6. The actual final 318 construction uses Gaussian **quadratic** prime patterns with cross-prime order separation. The distinct ordinary **affine** prime theorem used in the restricted-converse path only supplies same-prime order conditions. Neither one substitutes for the other.
7. The literal builder, raw/translated/sheared IR and both pinned manuscripts still match all recorded completeness hashes. The arithmetic supplement's whole-file hash changed. Its exact diff is only later height-section corrections: the chosen value satisfies 0<a<1; original versus shifted Faltings heights; the CM metric comparison; and the Gaudron–Rémond reference title. The completeness passage is unchanged. See `final-consumer-pins.json` and `excerpts/arithmetic-e96.diff`.
8. No new mathematical counterexample was found in these checks. Full PP, restricted converse and the actual source-arithmetic assembly must retain their exact scope. Kernel-checked finite order/CRT/trace identities do not by themselves prove the global analytic premise.

## Are separation and the preselected conditions already present?

Yes, as existing mathematical arguments, with partial formalization. The exact order-separation lemma and proof are byte-identical across V10–V13, SHA256 `9679890537544b5dcce5ec571542d5e7579c321a6b8706228035b0976ffe365e`; V11 lines 19700–19718. The real/local preselection is explicit in the actual318 assembly sections5–7. They are not placeholders for future plans. What remains is joined independent acceptance of the complete weighted analytic premise/current consumer and end-to-end formal assembly. `OrderSeparation.family_not_dvd` is a genuine finite theorem **assuming** positivity, size, odd/even parity, Hasse-error and spacing inequalities. It does not prove those hypotheses for a globally supplied prime pattern.

## Controlling protocol and independence

The current `docs/research-review/PROTOCOL.md` and `docs/audit-history/PROTOCOL.md` require a source application, not a bibliography: source hypotheses; constructed objects; domain/index coverage; transition/comparison maps; identity of the consumed object; coefficients/normalizations; local conditions; exceptional cases; and downstream consumption. `APPLICATIONS.json` gives required/constructed/match/evidence for each obligation in this lane.

The V11 exact target is fixed by `docs/manuscript-revisions/version11/kato-application.json` and its manuscript hash. Kato index coverage and limiting-class checks are assigned elsewhere. The V12/V13 application inventories are scoped revision records, not a replacement acceptance for all inherited arguments. Structural inventory validators and Lean axiom scans do not establish informal mathematical truth or the applicability of an external theorem to a different object.

This packet's author worked on the analytic modular comparison and is not its independent reviewer. The fresh source inspection of Mitsui is an independent inspection of those source pages, not a complete independent PP review. Model metadata beyond the execution identity is not asserted. Old component reviewer identities and exact reviewed hashes are retained in the copied inventory records; no new acceptance is inferred from their existence.

## The exact PP dependency chain

### A. Local sieve

Browning–Loughran Theorem 4.1 is applied to the actual five-variable rank-five isotropic quadric
`a²+b²−c²−d²−κw²=0`, with κ nonzero, squarefree modulus coprime to 2κ and arbitrary **nonzero** residue subsets. The n=5 boundary and uniformity in modulus/subsets matter. Möbius inversion imposes primitivity; the local factor becomes |Ω_l|/(l⁴−1). It is not permissible to include the zero residue or to read OCR's n>5 as the source's n≥5.

Browning–Heath-Brown Lemmas 2.1 and 4.1 are used for coprime inhomogeneous polynomials in boxes and covering rank-three quadratic congruences by lattices. The manuscript does not apply the homogeneous main theorem directly to inhomogeneous adjacent norms. It removes the zero right-hand-side and common-coordinate cases, checks polynomial content and the exceptional t=−2 case, and applies the lattice tail with the stated determinant/minimum bounds. The error constant may depend on the fixed thin-box parameter τ; the leading obstruction constant must not depend on τ or the later cutoff L.

Williams' fixed-modulus Mertens input supplies the sieve dimension and the logarithmic lower bound. The exact use is modulus 4, residues 1 and 3, or modulus 1 for the final product. It is not a uniform-in-modulus estimate.

### B. Fixed Gaussian field to centered nilsequences

The number field is E=Q(i). The Gaussian ray field and modulus H are fixed before each asymptotic. Only conjugation-invariant ray-class unions are used. The ideal weight counts two degree-one ideals over each selected split rational prime, so `T_C(p)=2 Λ'_C(p)`; prime powers and higher residue degrees are removed with square-root error. Finite Fourier inversion and the conditional density preserve that factor of two.

Mitsui Lemmas 14–15 apply to all finite-order ray characters at logarithmic finite modulus norm, including imprimitive characters. In the application `θ=χ(ρ∘Norm)` has modulus dividing m(q), norm at most Nm·q². For √X≤Y≤X use the fixed exponent 2B+1; below √X use the elementary ideal von Mangoldt bound. The inducing primitive character is trivial exactly for the main term. Removing extra Euler factors is an allowed equivalent argument with a separately bounded error. The rational version uses K=Q and exponent B+1. Complex-valued unsmoothing is justified by absolute values of the boundary sum, not positivity.

The subsequent Green–Tao applications are one-parameter results: quantitative Leibman, coordinate characterization, recurrence with arbitrary arc center, factorization and rational conjugation/metric comparisons. The norm pullback raises polynomial degree to 2d. Type II selects a positive-density row; it does not require every dilation to preserve equidistribution. Rational conjugation losses are fixed before the factorization exponent, which is fixed before the stronger Siegel–Walfisz exponent. The thirteen retained application rows bind these individual operations.

### C. Centered nilsequence estimate to polynomial count

The centered real weight is dominated by the ordinary prime weight. It is truncated to [L^(3/5),L] and multiplied by a fixed positive constant before the DK inverse theorem. For target U^s[L], the majorant satisfies U^(2s) on the full prime cyclic group. The short initial interval has an elementary negligible cube contribution.

The auxiliary cutoff z for this inverse-theorem argument is different from the polynomial cutoff v. Every fixed ray field/modulus, all unit residues and all required complexities/tolerances are handled before the physical size threshold is chosen. A diagonal step function is used; there is no uniform-in-varying-field theorem and no circular implicit z=z(N/V_z).

Green–Tao's ordinary-prime majorant and generalized von Neumann statements, Bienvenu's fixed affine-system correlation theorem, and Tao–Ziegler's local cube, arbitrary-function model, concatenation, generalized von Neumann and polynomial-forms estimates are consumed at their actual normalized weights. The bounded model is rescaled before applying the bounded-function result. For boundary strips the proof uses weighted second moments with independent parameter copies and a separated constant-shift factor, rather than counting strip points and multiplying by log^kN. The thirteen retained transference rows preserve these exact applications and their prior review scope.

### D. Ray densities and final quantifiers

Kopp–Lagarias supplies ray-class existence/reciprocity and the modulus exact sequence. Gaussian unit quotienting is already fixed at the base modulus 16; each new prime contributes the full residue-unit factor, with no extra factor of four. The norm-kernel/commutator calculation is made on the actual ray group; cyclotomic/disjoint-ramification comparisons give the exact conditional fiber. The varying field degree cancels fiberwise, so the lower bound is c(log L)^(-4k), with c independent of L.

Fix the coefficient forms and avoidance data. Choose one L so the obstruction bound is less than the lower bound, then fix that ray field and run its asymptotic. Only then use a τ_j→0 diagonal with thresholds allowed to depend on τ_j. The final width T is o(√N), while the lower range is retained. Coefficient replacement by q²c_j imposes the prescribed q|w and adjusts the required ratio before the theorem is invoked.

## Actual final 318 witness consumer

The consumer is `COMPLETENESS-ASSEMBLY.md`, not an arbitrary elliptic or modular curve. Its field is Q(√2); d=3−√2; E is y²=x³−d²x; P=2R0 for the displayed R0. Explicit nontorsion is sufficient for completeness. Rank-one or full-generator statements are not required in this direction.

Fix integer X, the scalar index and odd root labels, coherent roots h_i=−1/u([n_i]R0), their scales A_r, the compact real guard region, and the finite local-continuity modulus L. An initially chosen h0 may need adjustment inside its existing local neighborhood after the final roots and denominators are fixed; the current argument explicitly handles this rather than evaluating a new quotient at an unverified point.

For Θ={0,−1/2,−1,1/2399,−32/407}, choose D0 with D0²θ/A_r integral and use the **merged distinct** forms
`p_(r,θ)=u−(θ/A_r)D0²w²`.
Repeated positions are one prime, not illicit distinct copies. The θ=0 position and a nonzero θ ensure at least two distinct forms. The prime cutoff exceeds 76176 and all fixed bad factors. Prescribed w-divisibility handles the required local limits, and arbitrarily large u/w² handles the already fixed real bounds.

The Gaussian rays give the actual reduction orders d_±=Norm(π±1), with valuations v2(d_−)=6 and v2(d_+)=2. The consumer uses M_±=lcm(d_±/4), not the full orders. In addition to coprime cross-order factors, the separation refinement excludes selected primes from M_+ by combining the weighted count with w²≥N^(2/3), w²=o(N), spacing and Hasse's O(√N) bound. That refinement is not inferred merely from gcd(M_−,M_+)=1.

The resulting exact CRT system is
`h=0 mod Π³M_−`, `h=1 mod M_+`, `h=h0 mod L`.
The gcd(M_−,L)=16 condition and 16|h0 are essential. The real component-group factor is imposed before PP; the positive tail of the progression meets the chosen open real region. The selected branch uses the halving point R0 and the ray condition to obtain the actual reciprocal v=+1 branch, without imposing an incompatible extra p-power on h−1.

The detector has sixteen leaves, including four **unsquared** conjugated delta leaves. Its left-deep chain uses the exact m=1,4,13 weights. Even/odd valuation separation prevents cancellation, including zero leaves; the two-place reciprocal trace has residue 1 or 2 and is a unit. This is the checked finite `detector_trace_unit` consequence, not a replacement for PP. The real/local bounds yield the preparation-zero hypotheses for the three detector B values and scalar B. RC is then consumed through the actual pole theorem and the literal B/B³ conic normalization; that RC application is being audited in the contact lane.

Finally fill the literal 318 rational coordinates and all 288 rows, with denominator checks. The source's final constants are index 8 and orders 4/13, not historical alternatives. Current318FinalBridge and Current326Final still take `sourceArithmetic` explicitly. This packet does not remove that premise.

## Analytic modular lane and downstream identity

The formal all-cusp complex atlas is for the actual fine Γ1(N) case N≥5. All-level topological j properness is separately available. A general Γ_H complex atlas is not supplied by that theorem.

At torsion order three, actual complex evaluation of the literal short elliptic family gives a selected-scaling fiberwise additive comparison. The rank-eight algebra represents nonzero order-three points. Its full diamond/sign fixed algebra is canonically rank four and is the relevant coarse x-coordinate object. The central −I identifies ± in the effective upper-half-plane quotient. Therefore the rank-eight family is not the effective coarse Γ1(3) curve.

The recovered seven-module packet proves genuine wp(1/3) holomorphy in varying periods and a proper continuous finite-fiber surjective quotient map to **all literal fixed-algebra complex homomorphisms**, in the proven injective j,x coordinate topology. The four recovered infinity-germ modules give a local lift and exact scaling germs, not its linearity or lattice classification. Seven-module author replay/audit passed; the four-module combined audit and independent acceptance remain explicitly pending in their receipts unless superseded by a separately verified CI receipt.

These are genuine constructed objects, but none supplies the missing source injectivity/analytic algebraic isomorphism, global period-lattice classification, integral PEL/Jacobian identity, or Arakelov metric comparison needed by the contact-height application. Topological properness is not Scheme.Finite. N in `OpenJModel318.Base N` is a localization parameter, not a proof of general-N torsion. Do not use the analytic lane as a substitute for the actual global arithmetic comparison.

## Remaining work, in priority order

- Finish independent acceptance of the exact current PP-to-318 consumer contract, including weighted-count separation, parameter order, coherent branch, and final row identity. Preserve existing analytic component acceptances instead of rerunning unrelated proofs.
- Close final-typeset comparison for DK, Browning–Loughran and Browning–Heath-Brown if legitimate access is available. Otherwise retain explicit author-version status. No publication access restriction was bypassed.
- Finish the separate V11 Kato-index/class and RC-to-pole consumer reviews, then join those exact conclusions. They are not supplied by this packet.
- Decide the next necessary formal work from these exact dependencies. Do not continue unrelated modular proof expansion while this priority review is pending.
- The subsequent actual analytic/algebraic/PEL/Jacobian/metric comparison remains a distinct mathematical deliverable, not a citation cleanup and not something cured by a successful compiler audit.

## Reproduction and evidence

`build_inventory.py` binds the current repository files, existing application records, fresh source files and all nine-obligation contracts. `INPUT-PINS.json` records exact hashes. `retained-applications.json` preserves all 28 inherited analytic application rows with their source inventory paths. `revision-pp-bindings.json` records the exact full-appendix identity across V10–V13. `SOURCES.json` distinguishes fresh retrieval, inherited published checks, author versions and background-only sources. `APPLICATIONS.json` is this packet's new scoped contract inventory. `CHECKS.json` records lightweight manifest checks only; it is not a proof or independent review.
