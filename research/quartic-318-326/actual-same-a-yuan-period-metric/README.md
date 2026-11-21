# The original D=210 Kodaira–Spencer and Hodge metric, on one branch tensor

This appendix is for the reverse of the literal quartic 318/326 tables.
It concerns the actual selected polarized abelian surface A, not the
distinct modular Jacobian used for the modular-height bound.

1. [Actual principal period metric](principal-metric/ACTUAL-PRINCIPAL-PEL-PERIOD-AND-KS-METRIC.md):
   the principal Riemann form forces covolume 210 and gives the
   Hodge norm of the same rational determinant frame.
2. [Actual period cohomology and signed KS](period-cohomology/ACTUAL-PEL-PERIOD-COHOMOLOGY-BRIDGE.md):
   the first-order quotient is the actual Hodge quotient of deck
   periods; its polarization comparison gives the full determinant.
3. [The literal shared dt²](shared-dt/SHARED-DT-SQUARE-ARITHMETIC-ANALYTIC-NORMALIZATION.md):
   one arithmetic inverse coefficient is used at finite and infinite
   places. Changing an ordered form basis and its true dual gives
   a matrix congruence, so the archived complex KS scalar is derived
   in this same rational frame, not added as an independent input.

The exact [same-function-field cotangent](ordinary-and-finite/ACTUAL-NONCONTACT-COTANGENT-CONSTRUCTOR.md),
[the finite/archimedean branch comparison](ordinary-and-finite/ACTUAL-COTANGENT-FINITE-ARCH-JOIN.md),
and [the literal four-root axis](ordinary-and-finite/ACTUAL-FOUR-ROOT-ETALE-HANDOFF.md)
are included. The [actual fine-level overlap](geometric-context/THE-SAME-POINT-FINE-OVERLAP.md),
[universal family and unscaled KS](geometric-context/ACTUAL-UNIVERSAL-FAMILY-AND-UNSCALED-KS.md)
and [Čech connecting map](geometric-context/ACTUAL-YUAN-CECH-CONNECTING.md)
are also included as context. They identify the actual family, not
independent finite and complex realizations.

These are mathematical proofs and exact arithmetic replays. The
[primary reference is Yuan v2](https://arxiv.org/html/2205.11334v2).
The explicit PEL models, coherent GAGA and Picard/analytic comparisons
are used classically and are not claimed as native Lean producers.
There is no new reverse threshold, numerical period measurement or
forward claim. The signed trace convention in the appendix does not
assert a sign error in the source's rank-two bicanonical theorem.

The replays use Python 3's standard library:

    sha256sum -c SHA256SUMS
    sh replay.sh

Manifests in archived donor notes are their original workspace checks;
this appendix's manifest verifies the standalone published bytes.

Independent cold reviews:
[principal period](reviews/INDEPENDENT-PRINCIPAL-PEL-PERIOD-METRIC-REVIEW.md),
[actual period cohomology](reviews/INDEPENDENT-ACTUAL-PEL-PERIOD-COHOMOLOGY-REVIEW.md),
[shared dt²](reviews/INDEPENDENT-SHARED-DT-SQUARE-REVIEW.md),
and [the original cotangent and four-root chart](reviews/INDEPENDENT-ACTUAL-ORDINARY-FOUR-ROOT-REVIEW.md).
