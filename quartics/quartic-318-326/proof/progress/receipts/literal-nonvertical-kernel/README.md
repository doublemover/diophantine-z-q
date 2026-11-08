# Literal nonvertical tripling kernel

`LiteralNonverticalKernel318.isLimit` identifies the original full rank-eight torsion scheme as the categorical equalizer of the actual completed tripling composite and actual zero map restricted to D(2y), for every literal OpenJ base N. The universal property holds on arbitrary Scheme test objects, including nilpotents and nonaffine tests.

The proof directly applies the newly checked `LiteralSchemeCancellation318.tripling_zero_iff` to the actual D(2y) inclusion, then consumes the frozen actual completed doubling/negation equalizer. The inclusion is unchanged. This is not a new model, rank comparison, or set-theoretic point identification.

One source passed its strict first check; the recursive audit passed 20 declarations, using only propext, Classical.choice and Quot.sound. Independent review and hosted integration remain separate.

Still separate: proving every finite tripling-zero point belongs to D(2y), the global zero-section/complement decomposition, and the entire completed tripling kernel. No general-base associativity, packaged group object, PEL or final arithmetic construction is claimed.
