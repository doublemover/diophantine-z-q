# Two exact receivers for the unresolved zero-ordinate Cassels signs

These arithmetic reductions concern the **unchanged** linked scalar \(a=0,h=473592745039516333133760\) and the two exceptional denominator characters in the positive branch. The [immutable boundary and norm-admission packet](https://github.com/doublemover/diophantine-z-q/tree/7b1225cb968f6ab4e84ba887732814c574bb4bb7/research/quartic-318-326/actual-scalar-zero-ordinate-cassels-receivers) gives the original two quartics, exact test admission conditions, and the distinction between excluding one full lift and excluding a first-coordinate quartic. No assumption is made on the number of unseen primes.

1. [Exact modular crossed reduction](high-hom-1120/heegner-compressed-trace/actual-zero-ordinate-crossed-sign-modulus-r1/LITERAL-CROSSED-CASSELS-CHARACTERS-FROM-H-SIDE-MODULUS.md). It replaces expansion of the translated point \([i]P\) by modular division-polynomial evaluation and gcds on one \(h\)-side input. The simpler version uses \(B_0^{12}\); the staged version uses \(B_0^3,B_1^5,B^8\) and exact divisions. The still-unavailable \(h\)-side raw norm can have bitlength on the \(h^2\) scale. This is not a practical full computation for the original \(h\), and the signed arithmetic controls are synthetic.
2. [Fixed-field Artin reciprocity](high-hom-1120/heegner-compressed-trace/actual-zero-ordinate-fixed-artin-reciprocity-r1/FIXED-ARTIN-RECIPROCITY-FOR-THE-LITERAL-CROSSED-SIGNS.md). The two phases can instead be read as governed Frobenius character products on the hidden numerator support, with independently checked fixed constants. For a genuinely admitted test and complete \(\theta\)-support, root choice does not matter and no crossed denominator calculation is needed. Neither the hidden support nor the Frobenius products have been obtained on the literal input.

No sign, actual test admission, rational point, or original branch rejection is asserted. The linked prior packet's concrete two-conic admission tests remain separate.

## Independent review

- [Crossed-modulus exact signed receipt](independent-review-nov20/hom-actual-crossed-sign-modulus-cold-r1/INDEPENDENT-LITERAL-CROSSED-SIGN-MODULUS-REVIEW.md).
- [Fixed-Artin exact signed receipt](independent-review-nov20/hom-literal-fixed-artin-reciprocity-cold-r1/INDEPENDENT-LITERAL-FIXED-ARTIN-RECIPROCITY-REVIEW.md).

The older boundary proof is linked at its immutable public revision above, not duplicated in this packet. The two current proof manuscripts are preserved byte-for-byte.

## Exact short replay

    sha256sum -c SHA256SUMS
    bash replay.sh

This needs only Python 3 and standard shell tools. No Lean, network, factoring pass, or translated elliptic point expansion.
