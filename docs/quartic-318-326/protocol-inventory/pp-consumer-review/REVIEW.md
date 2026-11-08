# Independent review: Gaussian PP to the literal 318 consumer

Date: 2026-11-08. Reviewer: `/root/restart_hodge_gluing`.
Target author: `/root/restart_modular_curve`; this reviewer did not author the target inventory, the PP appendix, its current witness assembly, or the finite CRT/chain/row consumer proofs. Prior intrinsic Hodge work is outside this review.

## Decision and boundary

**Accepted as a bounded conditional application/consumer contract, not as acceptance of the complete PP proof, restricted converse, source arithmetic, or final theorem.** No mathematical mismatch was found in the parameter ordering, weighted-count separation, coherent branch/local choices, or the finite row-accounting join examined here. The application record accurately leaves the global producers and independent primary-source comparisons separate.

The exact reviewed author receipt is `recovery-modular-0358/input-inventory-v13/receipt.json`, SHA-256 `28eb39bd511dcbed2ae8872051090b6b416cec198c6f71f43464b0598a90f7fb`. The assigned mathematical target was Version 11, whole-source hash `1210d2e6f409e502fc9c95afc248fac16a9df48c760a396143780c20ec80b662`. Its Gaussian PP appendix, lines 16538–19168, and separation proof, lines 19700–19718, are byte-identical to the respective Version 10, 12 and 13 passages. The exact Version 13 whole hash and line shifts are in the bound author records. This permits this particular PP/separation carry-forward if Version 13 becomes active; it does not certify all other changes between versions.

In particular, Version 11's adjacent deep-completeness discussion uses exponent 19 and depth 20. The current literal 318 construction uses exponent 3, depths/orders 4 and 13, and the improved height route. These neighboring arguments are not claimed to be byte-identical. The current consumer has its own pinned assembly and builder/IR. Neither an old order-40/52 argument nor a product-of-factors detector may replace the current argument.

## What was independently read and checked

Fresh reading covered the author's PP-TO-LITERAL-318 nine-obligation entry and review, actual V11 PP theorem, weighted obstruction tail, fixed-field count statement, cutoff lower bound, final diagonal, and separation proof; the entire current COMPLETENESS-ASSEMBLY, branch and physical-anchor certificates; all PrimeCRTAssembly and NormChainCompleteness; the final arithmetic premise in Current318FinalBridge and all Current326Final. The relevant actual builder portions defining tests, leaf order, weights, detector, scalar and physical anchor were read. The generated row register was checked against all 288 actual IR row IDs and names, not only its summary counts.

This is not a new Lean replay, a reproof of all 288 row equations, a fresh proof of the analytic PP components, or a proof that the inventory contains every application. Existing primary-source and kernel-check evidence is preserved rather than relabelled as this reviewer's work.

## Nine obligations

### 1. Source hypotheses

Required: the fixed Gaussian PP theorem needs at least two distinct integer coefficients, a fixed divisibility parameter q, odd squarefree avoidance M with 7 not dividing M, and fixed lower bounds. Constructed: the three positive scales and five contact values yield rational coefficients; D0 clears all denominators and repeats are merged before applying PP. The zero contact and any nonzero contact ensure at least two distinct forms. Taking w divisible by the requested q handles the prescribed local depths after the fixed dilation. All roots, scales, continuity data, bad factors and thresholds precede PP.

Match: this is exactly a fixed-data application, not a uniform estimate while varying the field or modulus. The theorem's q=1 reduction replaces coefficients by q² times their values and adjusts the ratio threshold. Evidence: V11 thm:v5-simultaneous-primes and current assembly §§2–5.

### 2. Constructed objects

Required: one compatible set of witnesses for the actual construction. Constructed: K=Q(sqrt(2)), E:y²=x³−(3−sqrt(2))²x, R0=(1+sqrt(2),2sqrt(2)), P=2R0; the fixed scalar point, positive odd Lucas labels, globally coherent half-point charts and root product determine the scales. These are the curve and functions in the current builder, not a substitute modular curve or the other elliptic curve used by RC.

Match: the builder and all three IR hashes equal their recorded historical values. The observed IR has 318 coordinates, 80 free coordinates including the input, and 238 generated coordinates. Evidence: assembly §§1–4, builder lines 337–458 and 540–616, final-consumer-pins, fresh CHECKS.json.

### 3. Domain and index coverage

Required: all three detectors and all five contacts, the finite avoidance data, and every actual source row. Constructed: merge the 3×5 contact forms rather than discarding any condition; retain cutoff greater than 76176 and every fixed bad/root/scale/continuity factor. The selected primes exceed all these factors. The final register covers IDs 0 through 287 once each and with exactly the current names.

Match: generated rows comprise 188 quadratic assignments, 16 rational quotients and 34 field-quotient components. Structural rows comprise 16 reciprocal-chart, 3 compressed-anchor, 14 nondegenerate-weight, 6 detector-trace, 8 pole, 2 scalar-Kummer and 1 physical-anchor rows, totaling 50. This establishes finite coverage, not that the global witnesses satisfying these rows have been constructed in Lean. Evidence: assembly §§5,9; row-coverage.json; direct IR comparison.

### 4. Transition and comparison maps

Required: translate full reduction orders to doubling-image orders, assemble CRT, select the literal coherent branch, and convert pole conventions. Constructed: d±=N(pi±1) are full elliptic group orders; M±=lcm(d±/4), since full rational two-torsion gives kernel size four. PP gives gcd(M−,M+)=1 and gcd(M−,L)=16; separation separately gives gcd(Pi,M+)=1. Together with the cutoff and 16 dividing h0 these are exactly the premises of the Pi³ CRT.

Match: PrimeCRTAssembly retains every coprimality and divisibility premise and separately states that it proves congruences, not real orbit density. The fixed branch uses R0 in the doubling image, not merely P=2R0. The branch certificate derives 2 as a fourth power from the Gaussian ray, treats both roots of 2, constructs an explicit half of R0, and excludes p=2,7. Hence the globally fixed v-chart takes +1 at the opposite place without a new incompatible p-power condition on h−1. The B/B³ conic residual normalization remains the separately assigned RC/pole interface. Evidence: CRT module, BRANCH-CERTIFICATE and assembly §§5–8.

### 5. Identity of the consumed object

Required: the literal detector and final polynomial, not a similarly named old source. Constructed: the builder makes sixteen left-deep leaves, twelve squares and four unsquared conjugated delta/parity leaves; weights use m=1,4,13 and Wnext=W²+q_m leaf. Three full sixteen-step chains occur in the actual IR.

Match: NormChainCompleteness takes odd weight valuations and even leaf valuations (including a zero leaf), and proves the two reciprocal contributions have residue 1 and either 0 or 1. In odd characteristic their trace is a unit. Its hypotheses are precisely the local conditions still supplied by the arithmetic assembly. The rational trace variable encodes N(W)/(2w0); the physical detector B agrees with 1/(e delta) divided by the square of the reciprocal trace. The final source-to-polynomial and 326 lift preserve the input but do not supply sourceArithmetic. Evidence: builder lines 554–614, 733–783; NormChainCompleteness; final bridge endpoints.

### 6. Coefficient and normalization conventions

Required: maintain exact constants, both embeddings and integral valuation factors. Constructed: v2(d−)=6 and v2(d+)=2 become v2(M−)=4 and v2(M+)=0 after division by four. The factor 64 in h0 and L handles the component of R0 even when the original component order was measured with P=2R0. The fixed scalar coefficient is 114444, with local scalar valuation 4 at 2 rather than the older value 6. The actual S is 3^65536 and the physical anchor is N(uR)+4096 S nC.

Match: these constants are present in the current builder and certificates. The retained source prime convention uses arithmetic Frobenius; this review makes no assertion of replacing it by geometric Frobenius. The actual weight formulas are q4=e^7/delta³ and q13=e^25/delta³. A stale comment at builder line 617 mentions historical q16/q52; the executable formulas and consumed record use q4/q13. This is a nonblocking comment correction to queue, not a change to the checked construction.

### 7. Local conditions

Required: compatible finite-adic conditions and nonempty real domain with all quotients defined, before prime selection. Constructed: coherent roots are fixed first. If newly introduced quotients are undefined at an earlier h0, the assembly explicitly adjusts h0 inside the old finite-adic neighborhood and the open real complement before fixing L. The root values are treated on the hR0 orbit, not asserted to be single-valued functions of H=hP. A compact subset K0 of the good real region provides uniform bounds, and the component-killing factor makes the later CRT progression dense in the same connected orbit component.

Match: this removes retrospective sign, root or threshold choices. Local q-divisibility at 2,3,17 and sufficiently large lambda make the three detector B values and scalar B satisfy the pole hypotheses. The physical-anchor certificate handles every finite prime and the real place, then proves the homogeneous solution has nonzero affine denominator by ternary anisotropy. It still invokes standard p-adic square/Hensel and Hasse–Minkowski inputs explicitly. Evidence: assembly §§3–8; ANCHOR-COMPLETENESS.

### 8. Exceptional cases

Required: ensure selected primes do not divide any opposite order, deal with h=0,1, zero leaves, zero denominators, and repeated contact forms. Constructed: use the stronger weighted count, not only the PP existence statement. With all fields/moduli fixed first, slow the diagonal tau(N) so tau(N)N^(1/6)/(log N)^k tends to infinity. The strip w<N^(1/3) has weight O(N^(4/3)(log N)^k)=o(NT), so a pattern remains with w² at least N^(2/3) but o(N).

Match: Hasse gives d+(p_j)=p_j+O(sqrt N). All ratios d+(p_j)/p_i are eventually between 1/2 and 2, so divisibility forces equality. Distinct positions have separation at least c_*N^(2/3), contradicting the Hasse error; equal positions are excluded because 4 divides the full order and p is odd. Only afterward pass to d+/4 and its lcm. The CRT progression permits h>1. Valuation induction explicitly includes zero leaves; positive B excludes the zero-fibre division in completeness. Evidence: actual V11 separation lines 19700–19718, weighted tail/count/diagonal, finite CRT and chain modules.

### 9. Downstream consumption

Required: construct rational witnesses for every integer input, then obtain the actual polynomial equivalence. Constructed: the current assembly is conditional on the global PP and RC/pole inputs and the stated standard arithmetic/topological ingredients. Given these it explains how to fill the free variables and generated quotients with their nonzero denominators, then the structural rows. Current318FinalBridge.defines_integers_of_source_arithmetic and Current326Final explicitly retain sourceArithmetic.

Match: a finite row accounting, source replay, or canonical 326 lift neither proves global PP nor RC nor discharges the integer-to-witness direction. The improved height/PEL/Arakelov route and the Kato/RC joins are separate reviews, not inferred from this one. Evidence: assembly §10 and exact final endpoint types.

## Source-version and current-working-tree limits

The existing 28 analytic application records and Mitsui's fresh published retrieval are preserved. This review did not freshly re-prove those analytic components. The author's missing final-typeset comparisons for Dodos–Kanellopoulos, Browning–Loughran and Browning–Heath-Brown remain open. No access restriction was bypassed. There is no blanket PP acceptance.

The 81 lightweight checks pass against the frozen target, with one explicitly recorded concurrent working-tree drift: arithmetic.md changed from b2a744f8…a09469 to 9737d564…ee518 during review. The frozen bytes are recoverable at commit 09e35ad61946e92561460d93c3e57831ea5e3117. The saved diff changes only the later Kato section beginning at line 1591; the first 1258 lines used for this PP join remain byte-identical. Checkpoint confirmed that adoption and a further V13 label carry-forward are its work. Old receipts are not rewritten or silently rebound.

The author's V13 labels in its PP application evidence are navigational shorthand: the exact V11 and V13 byte/line bindings independently checked here remove ambiguity. No mathematical repair is requested for that shorthand. Future overall acceptance must still resolve the retained source comparisons and independently join the actual global PP/RC/height and witness producers.
