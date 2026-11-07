# Literal scalar contact to actual local depth

## Result and exact boundary

`ScalarPlaceBridge318.source_scalar_place` now constructs an actual normalized valuation above each consumed scalar contact prime, directly from the literal raw source constraints. At the selected place it proves:

- v(f_H)>0;
- v(f_R)>0;
- v(f_R/f_H)≥16;
- rational scalars retain the ordinary p-adic valuation.

The theorem assumes only the raw `Constraints (stage0 S) w`, a prime p not dividing 2, 3, 7, 11, or 17, and a positive odd finite value R=v_p(r). The parameter r is explicitly bound to the actual four-factor scalar contact polynomial in beta=3723(2X+1)². There is no real-sign, abstract-place-existence, local-evenness, norm-formula, group-label, logarithm, or sourceArithmetic premise in this final theorem.

This is the valuation portion of the current order8 scalar argument, not the historical order32 argument. To conclude p⁸ divides the scalar integer label c, the remaining work must still identify the actual point labels and pass the torsion-safe doubled group identity through an actual local logarithm homomorphism/isometry. This packet deliberately does not assert that final integer divisibility. In particular, a logarithm proved only over Q_p does not cover the genuine inert branch: that branch requires an unramified quadratic local realization/logarithm extension or an equivalent local-group argument.

## Modules

### ScalarSource318

Decodes the exact scalar rows 265–281 and input rows 79,263–264. It proves the r inverse equation, emitted inverse power16, the separate division by n_H/r, nonzero Q and n_H, the cleared pole relation, and the effective formula

Q = n_R/(n_H r¹⁵).

It proves N=Norm(1+f_H/r), Norm(f_R/f_H)=(n_R/n_H)², and

r=(beta−1)(beta−2401)(32 beta+343)(2 beta−1).

The proof does not discard a zero normalizer branch globally. At a positive contact, the normalizer 1+114444r is a valuation unit, which is sufficient for local soundness.

### ScalarPoleValuation318

Proves zero-safe noncancellation in W=N²+rQ², with the N=0 branch included. Odd v(r) separates the even and odd summand values. The exact retained scalar pole rows then give

4 v_p(N)>−R and 4 v_p(Q)>−3R.

The effective exponent15 implies v_p(n_R/n_H)≥15, hence v_p(Norm(f_R/f_H))≥30. Every pole, quotient, and norm relation here is consumed from the literal source decoder.

### ScalarLocalValues318

Proves even abscissa valuation directly from y²=x³−Dx at a D-unit place. The zero-ordinate case is allowed. This yields even valuation of actual f_H from the source curve. Actual f_R is the square of the inverse scalar root, so its even valuation follows directly. The shifted norm factors have values min(0,v(f_H)−R), because an even value cannot equal odd R.

### ScalarPlaceBridge318

Combines the nonpositive shifted-factor norm values with the strict N bound to prove positive f_H value at both split places. The norm-ratio order30, together with even local ratio values, gives ratio order at least16 at one place.

The inert case repeats the same normalized inert valuation twice in the two-place argument, exactly accounting for residue degree2 without replacing v(p)=1 by v(p)=2. The actual inert valuation and Hensel construction are imported from the independently reviewed inert-place packet. A residue-field case split then constructs the required actual place without assuming a square root or local realization.

## Source and validation

The mathematical target is `quartics/quartic-318-326/docs/arithmetic.md`, “Scalar divisibility without a real-sign assumption,” equations (12)–(18). The emitted construction is `construction/318/build_source.cjs`, lines 786–845. The statement stops before the logarithm and label step (19).

Run `bash scalar-place-bridge/run.sh` from the scratch root. Lean 4.35.0 fresh-builds all four modules with `-Ddebug.skipKernelTC=false`. The complete recursive axiom audit passes 52 declarations across 4 modules, permitting only `propext`, `Classical.choice`, and `Quot.sound`. No admitted proofs or native-decide axioms occur. Exact file and dependency hashes are in `receipt.json`. Local soundness independently copied and rebuilt all four modules and passed the same 52-declaration recursive audit, with no mismatch; its receipt is `soundness-local/scalar-peer-review/REVIEW.md`.
