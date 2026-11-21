# Exact chosen Gaussian primary Frobenius

Read [the proof](author/EXACT-GAUSSIAN-PRIMARY-FROBENIUS.md) and its
[independent signed review](independent/INDEPENDENT-PRIMARY-FROBENIUS-ALL-RESIDUAL-POINTS-REVIEW.md).
The companion [stationary residual derivative proof](companion/GAUSSIAN-RESIDUAL-DERIVATIVE.md)
and its [independent review](companion/INDEPENDENT-GAUSSIAN-RESIDUAL-DERIVATIVE-REVIEW.md)
are included for offline cross-checking.

At the chosen Gaussian prime, the proof derives exact coordinate p-power
on all actual residual points over any extension of the prime field,
using explicitly identified classical complex uniformization. This does
not assert arithmetic torsion transport or a Lean build, a prime
distribution theorem, or rational solutions of the original quartic.

    sha256sum -c SHA256SUMS
    (cd author && python control.py | cmp - CONTROL.txt)
