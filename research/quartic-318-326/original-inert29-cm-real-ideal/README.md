# A fixed totally real CM replacement for the original detector residue

The signed products use two fixed level-48 Hecke functions and eight **complete** ordinary CM packets in one auxiliary imaginary field. Each packet includes its whole class-square orbit, both local Frobenius arms, and global complex conjugation. The exact result matches the original cubic phase on all 224 ordered supersingular flags at 29.

The calibration coefficients lie in the fixed totally real field \(\mathbb Q(\sqrt5,\sqrt6)\). The same actual genus-half ratio for either odd target lies in a field of degree at most eight and is inverted by complex conjugation; its **oriented fractional ideal** therefore determines the cubic residue. Neither an absolute norm nor unlabelled prime pairs suffice. No moving ideal exponent, moving residue, target rank, or rational marked point is computed. A cube does not exclude an order-three phase.

- [Exact proof and whole-packet replay](source/high-hom-1120/heegner-compressed-trace/original-inert29-CM-real-ideal-r2/REAL-CM-DIVISORS-AND-THE-ORIENTED-IDEAL-INPUT.md)
- [Independent signed review](independent-review/INDEPENDENT-CM-REAL-IDEAL-REVIEW.md)
- [Earlier symmetric conductor-independent CM function](source/high-hom-1120/heegner-compressed-trace/original-inert29-CM-supported-cubic-r1/AN-EXACT-CM-SUPPORTED-CUBIC-READOUT.md)

Run sh verify.sh with Python 3, SymPy, cmp and sha256sum. It checks both fixed finite replays and all exact file hashes, not a moving class orbit or ideal factorization.
