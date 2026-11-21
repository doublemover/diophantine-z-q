# Optimal class-character order for the first selected detector arm

For the actual first balanced arm \(u=1,\ v=\theta\), without a repair prime and with \(q_0\equiv7\bmod24\), no character of order eight or less detects the marked relative ideal class. The exact minimal order is \(2^{m+2}\), where \(2^m\) is the sole cyclic factor of order at least four of the corresponding quadratic field's 2-class group. A compatible shared-final-prime refinement forces \(m=2\), guaranteeing an unramified character of order sixteen that detects the mark class. No signed Heegner ideal, rational mark, or rank is evaluated.

- [Same-index prime refinement and quartic gate](prime-refinement/ACTUAL-CM192-OCTIC-GATE-AND-CONIC-REFINEMENT.md)
- [Exact optimal character existence and four-field replay](optimal-character/ACTUAL-CM192-EXACT-MINIMAL-SEPARATING-ORDER.md)
- [Signed independent review](independent-review/INDEPENDENT-CM192-EXACT-SEPARATING-ORDER-REVIEW.md)

    (cd optimal-character && python3 -B replay_four_imaginary_genus_kernels.py | cmp - EXACT-FOUR-IMAGINARY-GENUS-KERNELS.json)
    sha256sum -c SHA256SUMS
