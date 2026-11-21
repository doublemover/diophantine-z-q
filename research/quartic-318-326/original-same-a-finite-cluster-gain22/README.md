# The same-A height estimate with a +22 offset

The [new estimate](SAME-PAIR-FINITE-CONTACT-CLUSTER-GAIN.md) uses the exact two old tensors from the reverse proofs for 318 and 326. The four contacts form one triple and one isolated residue at 2, 3, 5 and 7. Their gaps control all finite factors. The actual four-root cover improves the dyadic divisibility further; neither the cover's naive integral equation nor a recomputed Kodaira–Spencer map on the height trait is used.

The unchanged pair is divisible at every finite place by the common rational integer 1,189,580,636,160,000 in the actual Néron Hodge lattice. The product formula subtracts the logarithm of this integer from the unchanged archimedean estimate. Thus the directional comparison for this same selected A has offset strictly less than 22. Without the arithmetic square-root step the same argument gives an offset strictly less than 23. The older +64 reverse argument remains valid as stated. No polynomial, tail selector, marking, CM/non-CM field, or native constant is changed.

The [new independent review](review/INDEPENDENT-ACTUAL-SAME-A-FINITE-CLUSTER-GAIN22-REVIEW.md) checks both exact offsets and the full scope of the finite gain.

The background contains the exact old reverse and arithmetic four-root papers and their finite constant replays, plus the two signed KS specialization proofs. Their existing independent receipts are included separately from the new independent review. This is a paper arithmetic strengthening, not a compiled theorem or evidence about a separate ring suite.

Reproduce with Python 3 and POSIX shell:

    sha256sum -c SHA256SUMS
    python3 check_contact_cluster_gain.py | cmp - EXACT-SAME-PAIR-CLUSTER-GAIN.json
    python3 background/replay_d210_twists.py | cmp - background/EXACT-D210-TWISTS.json
    python3 background/check_reverse_constants.py | cmp - background/EXACT-REVERSE-CONSTANTS.json

The replays check exact integers, rational field data and finite controls only. The proof's vertical argument applies also to extensions of the residue field, as explained in the proof.
