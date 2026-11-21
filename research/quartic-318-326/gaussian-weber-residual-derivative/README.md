# Actual Gaussian residual derivative and prime-ring normalization

Read [the proof](author/GAUSSIAN-RESIDUAL-DERIVATIVE.md) with its
[independent signed review](independent/INDEPENDENT-GAUSSIAN-RESIDUAL-DERIVATIVE-REVIEW.md).

The paper proves that the literal residual Gaussian scalar has
stationary rational abscissa at the chosen residue root. For the
additional explicitly stated finite-abscissa degree cut, the actual
prime-field coordinates are one of the four turns of Frobenius.
Primary-unit calibration and the characteristic-zero degree producer
are outside this bundle.

This is a mathematically reviewed paper proof, not a Lean build or
a rational point result. The included finite controls independently
exercise the cleared mixed chord and quotient jets. Verify or replay:

    sha256sum -c SHA256SUMS
    (cd author && python control.py | cmp - CONTROL.txt)
