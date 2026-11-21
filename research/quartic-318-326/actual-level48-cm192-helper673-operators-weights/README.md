# Fixed operators and all literal marked weights at helper 673

The receiver at 673 has an exact 1,008-row degree-17 transition table and a 56-row relative Frobenius table, expressed in a common set of rigid frame bases. A separate replay identifies every one of the 5,376 literal level-48 supersingular flags with its exact unordered subgroup pair, ordered modular chart and chosen frame lift. It gives all 1,368 orbit weights for the unsigned parity calculation.

These are fixed ingredients. No selected detector discriminant, moving-prime operator, entire product, output mark, rank, or rational point is claimed.

- [Fixed degree-17 and relative Frobenius operators](ct-level48-cm192-helper673-framed-t17-r1/EXACT-HELPER673-COMPRESSED-FRAMED-T17.md)
- [Literal flags and parity weights](ct-level48-cm192-helper673-marked-parity-weights-r1/EXACT-HELPER673-MARKED-SUPERSINGULAR-PARITY-WEIGHTS.md)
- [Signed independent review](independent-review/INDEPENDENT-CM192-673-FIXED-OPERATORS-AND-WEIGHTS-REVIEW.md)

    sha256sum -c SHA256SUMS
    (cd ct-level48-cm192-helper673-framed-t17-r1 && python3 -B replay_helper673_framed_t17.py | cmp - EXACT-HELPER673-FRAMED-T17.json)
    (cd ct-level48-cm192-helper673-marked-parity-weights-r1 && python3 -B replay_helper673_exact_weighted_flags.py | cmp - EXACT-HELPER673-WEIGHTED-FLAGS.json)
