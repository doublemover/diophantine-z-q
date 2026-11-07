# Source arithmetic: remaining proof obligations

This is an implementation map, not a proof of these assertions. The concrete Lean bundles prove the complete polynomial-to-raw-source algebraic equivalence and exact degree four. Their integer-definition theorem still assumes the source arithmetic. Local lemmas listed below reduce some bookkeeping but do not remove that global dependency.

## Final interface already checked

`ArithmeticSeparation.LabelSeparation beta` packages an integer label, a natural modulus dividing the numerator of beta minus that label, and a strict numerator-size bound below that modulus. Lean proves equality with the integer label. `OddLabelSeparation` also carries oddness, allowing the one-gate input beta=3723(2q+1)^2. The prior nested-square input has its own checked denominator bridge. Integer-input completeness remains a separate hypothesis.

The global source proof must actually construct these certificates and all witnesses. It is not enough to assume that the polynomial already characterizes integers under another name.

## Global soundness obligations

1. **Concrete curve and group structure.** Establish the required rank, torsion, chosen generator and square-abscissa statements over Q(sqrt(2)). Recover the correct labels from every source chart. In the relaxed H chart, the label can be a half-integer; local comparisons must explicitly allow denominators2 at the consumed odd primes.
2. **All exceptional branches.** Treat Ui or Vi equal to the identity and the V0=identity branch. Prove logarithm denominators and polynomial factors are nonzero where used. Guarded root quotients require nonzero real difference, hence nonzero field determinant; the latter elementary implication is checked in `ConcreteQuadraticDomains`.
3. **Pole obstruction and norm-chain valuations.** Derive the exact valuation recursions from the algebraic source. `NormChainExtraction` then proves all leaf orders at one common split place, including odd-parity no-cancellation and trace selection. `NormChainZero` proves an algebraic zero-chain alternative only for actual square leaves. The newer linear-delta leaves are not globally squares, so that argument must not be reused: derive their intrinsic even local valuation and use odd-contact noncancellation to show that a zero chain has no consumed contacts. `ValuationCurveParity` now derives the intrinsic delta parity directly for Mathlib discrete additive valuations from the curve equation and the unit conditions on2,D, including zero-coordinate cases. `ValuationEvenNormChain` proves actual odd/even noncancellation, the exact finite step valuation and the arbitrary-length zero-chain exclusion at such a contact place. The number-field places, the contact valuations of the source weights, and the trace/pole-to-threshold connection still must be established.
4. **Place orientation and logarithm comparisons.** Use the rational H/V0 norm tests, retained Ui tests and Lucas residual to select the correct formal place. Prove all truncated-log error bounds and their applicability to half-integer H labels. `ReciprocalDeltaLog` and the Padé modules check exact composition/remainder identities, not the local error theorem. The Padé3/2 numerator and denominator nonvanishing is global in Q(sqrt(2)); the Padé2/1 denominators require the actual square-argument or reciprocal-curve hypotheses, which are now checked explicitly.
5. **Global height versus modulus.** Relate actual root and scale coordinates to the input and labels. Supply the contact-radical bounds and constants, then derive the strict numerator-size inequality in the separation certificate. Handle beta=0 separately in the odd-affine input branch.

## Separate height-transfer dependencies

Do not package the current height49/8 argument as one unexplained generic height assertion. Its dependencies are distinct:

1. **Modular realization and local signs.** Construct the required modular realization, its level/degree estimates and the relevant real-sign splitting. Verify the exact hypotheses of the cited Pan input.
2. **Actual image and isogeny estimate.** Apply the fixed-dimensional Gaudron–Rémond estimate to the actual dimension-two image with its stated height normalization. Do not reintroduce an unproved polarization requirement or silently use a larger ambient Jacobian.
3. **Finite divisor estimate.** Prove the ramification-divisor inequality and the nonpositive contribution from the explicitly effective finite divisor, with vertical support accounted for.
4. **Archimedean metric calculation.** Prove the exact cotangent metric cancellation and the Cauchy bound in the normalization used by the height statement. The earlier Green normalization audit does not by itself establish this revised argument.
5. **Numerical transfer and contact exponents.** Combine those estimates to obtain the stated49/8 exponent, constants and final strict separation bound. Then verify that the order4/order13 Padé errors and scalar index bound exceed the required margins.

The workers' independent mathematical audits support the current derivation, but these analytic and arithmetic steps have not been formalized here. The literal Padé coefficient identities and denominator domains are separate kernel-checked results.

## Global completeness obligations

1. **Restricted pole completeness.** The principal deep input is V10's restricted converse from full2-primary Selmer corank1 to analytic rank1, followed by the simultaneous descent construction. The fixed-form even-scalar bound is asserted uniformly in the elementary2-group and varying conductor support. Its positive-complex and central-calibration proofs need an independent arithmetic audit. Kato1999 Theorem0.8's p=2 citation has been checked separately; that check does not prove the new uniform bounds.
2. **Preparation-zero scalar.** Check every original pole hypothesis for b=a(W/(1+a))^2: positivity and smallness for integer inputs, square reduced denominator, exact local thresholds, and W a unit at each prime dividing a. The odd-input source must use its global2-adic nonsquare argument for domains rather than false global real positivity of r.
3. **Prime selection and canonical branch.** Verify that the Gaussian-prime construction simultaneously supports all prescribed local rays, continuity choices and reciprocal branch constraints. Chosen-ray properties used in completeness are not assumptions available for arbitrary soundness witnesses.
4. **Real avoidance.** Impose the fixed component-group divisibility before selecting the progression. Avoid the four real-part root-difference zero loci inside the existing positive-measure scalar region. The independent mathematical argument is in `independent-audits/real-part-root-guards/PROOF.md`; it is not yet formalized in Lean.
5. **Actual rational witness assembly.** Produce all circuit coordinates, including scalar and detector pole witnesses, with the exact chosen fixed coefficient S. Then the already-checked raw-source replay and sum-of-squares theorem transport these witnesses to the literal polynomial.

## Useful source locations

- Pinned upstream commit: ba7a3e0a0c171b7cd2ce75976addba57fad8a5dd.
- `upstream-v10/manuscripts/quartic_v10.tex`: pole completeness and restricted converse near lines1040–1135; fixed-form even scalar near1949–2090; real progression near10632–10692; Kato comparison near12663–12720; uniform integral positive complex near12832–13075.
- `notes/v10/norm-v0-orientation-and-base-weight.md`.
- `notes/v10/reciprocal-log-branch-rescue.md`.
- `notes/v10/odd-linear-square-input.md`.
- `primary-source-audits/kato1999/AUDIT.md`.

No unconditional source arithmetic theorem or global variable minimum is claimed here.
