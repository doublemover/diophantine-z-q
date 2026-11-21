# A sharper selected-pair family, and the limit of changing the scalar preparation

Two independently reviewed counting statements for the original 318/326
forward argument:

1. **Lower bound after choosing a fixed eligible pair.** With the actual
   fixed companion squareclass \(\theta\), there are
   \(\gg X/(\log X)^{1-2^{-\omega(\theta)-5}}\) distinct common
   squarefree enlargements in \((X,2X]\) that preserve the original mark
   and both exact full 2-Selmer sizes eight. The original pair and its
   omitted prime are kept. The exponent is independent of the number
   of already fixed base or helper primes; constants may depend on
   the seed and companion.
2. **Upper bound allowing every scalar preparation at one integer
   input.** The scalar's squareclass \(\beta(a)\) is unchanged by
   changing the source index, labels, or auxiliary choices. Both
   marked twist coordinates, over all those choices, lie in a family
   of size \(O_a(X/\sqrt{\log X})\). Hence an ordinary ambient
   density-one rank statement cannot by itself force a scalar witness.

These count different families. Neither proves a rational PointPair, a
rank result, a new numerical pole, a final polynomial solution, or a
Lean verification. The two copied Lean files are exact historical source
pins for the scalar formula, not a compilable intake.

- [Pooled reserve proof](rc-native-helper-20261120/ct-original-pooled-reserve-prime-r1/POOLED-OLD-INCIDENCE-RESERVE-PRIME.md)
- [Fixed-input scalar proof](rc-native-helper-20261120/ct-original-scalar-union-thinness-r1/SCALAR-RETUNING-DOES-NOT-THICKEN-THE-MARK.md)
- [Signed independent review of both](independent-review-nov20/rc-pooled-reserve-and-fixed-scalar-thinness-cold-r1/INDEPENDENT-POOLED-RESERVE-AND-FIXED-SCALAR-REVIEW.md)

Run from this folder (the exact finite replays use only Python's
standard library; the asymptotic counts are paper proofs):

    sha256sum -c SHA256SUMS
    (cd rc-native-helper-20261120/ct-original-pooled-reserve-prime-r1 && \
      python3 -B replay_pooled_reserve.py | cmp - EXACT-POOLED-RESERVE-CONTROL.json)
    (cd rc-native-helper-20261120/ct-original-scalar-union-thinness-r1 && \
      python3 -B replay_literal_scalar_support.py | cmp - EXACT-LITERAL-SCALAR-SUPPORT.json)

Earlier context is retained for the relative links. The two older
context manifests retain historical hashes without vendoring their
whole dependency sets.
