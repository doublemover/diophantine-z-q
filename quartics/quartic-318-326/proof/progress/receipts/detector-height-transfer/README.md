# Actual detector-scale height transfer

This isolated packet closes the source seam in `quartics/quartic-318-326/docs/arithmetic.md`, “Height transfer with the existing constant” (lines1148–1167 in the audited revision). It does not prove the five-contact/Arakelov estimate that supplies the three detector heights.

## Checked result

For the actual quadratic field K=Q(sqrt(2)), x in K, and the literal rational quantities

- n = x.norm,
- B = x.re + n,

`DetectorHeightTransfer318.actual_norm_49_over_8_height` proves

h(x²) < 7 H |N|^(49/(8k))

from H≥1, N≠0, lambda≠0, and the three actual absolute-height inequalities

h(lambda), h(B² lambda), h(n² lambda) ≤ (H+log3)|N|^(49/(8k)).

Here h is exactly `NumberField.absLogHeight₁`, not an abstract replacement. The statement includes rational x, zero x, repeated source factors, and all natural k; Lean's k=0 division convention is harmless, though the source uses a positive count. No B≠0 or n≠0 assumption is needed for this height lemma.

The nonzero-lambda premise is essential. Without it, all three detector heights vanish independently of B and n. The literal detector must supply it; this packet does not silently infer it from height inequalities.

## Proof

1. The rational absolute-height normalization is discharged by the independently checked actual number-field height formula. Height inversion, submultiplicativity and exact square scaling give h(B),h(n)≤T.
2. Write x=u+v sqrt(2). From B=u+n and n=u²−2v², use the actual numerator/denominator data of B and n to construct the integer quadratic

   a = den(B) den(n),
   b = −2 num(B) den(n) + 2 num(n) den(B),
   c = num(n) den(B).

   Its actual root is x. Every coefficient has absolute value at most 4 H(B)H(n), where H(q)=max(|num(q)|,den(q)) is proved to be exp(h(q)).
3. The previously checked `PrimitiveQuadratic318.primitive_triple` divides by the actual gcd. Positive gcd division cannot increase this coefficient bound.
4. For v≠0, the independently proved actual primitive-quadratic identity `PrimitiveQuadraticMahler318.primitive_height_identity` identifies the Mahler measure with exp(2h(x)). Mathlib's Landau inequality bounds it by sqrt3 times the coefficient sup norm. Taking logarithms yields exactly

   2h(x) ≤ h(B)+h(n)+log4+(1/2)log3.

5. For v=0, n=u² and exact rational square-height scaling gives the same inequality directly. Thus no irreducibility hypothesis leaks into the final result.
6. The actual absolute height on K satisfies h(x²)=2h(x), using its independently proved degree-two normalization, including rational x.
7. Mathlib's certified logarithm bounds give 2+2log3+log4+(1/2)log3<7. With H≥1 and W≥1 this absorbs the additive constants into7HW. For N≠0, W=|N|^(49/(8k))≥1 is proved directly.

## Validation and scope

Run `./build.sh`. Both the module and complete axiom audit are rebuilt with `-Ddebug.skipKernelTC=false`. All25 public theorems have only `propext`, `Classical.choice`, and `Quot.sound` as axiom roots. There are no custom axioms or admitted proofs. `receipt.json` records exact source/dependency hashes.

The packet consumes the prior checked primitive/Mahler/absolute-height modules in `converse-work/height-box-interface` and ordinary Mathlib results. It does not discharge the three upstream detector-height estimates, the five-contact geometric/Arakelov theorem, odd-label finite-place sign compatibility, or the final source circuit decoding. Those remain separate assembly lanes. No repository file or PR was changed.

The API also supplies arbitrary nonnegative real exponents (`actual_norm_exponent_height`). The earlier19/k wrapper is preserved only for the historical section1148 transfer. The adopted refinement at arithmetic.md1348–1446 uses49/(8k). Independent source/normalization review and full copied kernel rebuild: `converse-work/detector-transfer-review/REVIEW.md` and its receipt.
