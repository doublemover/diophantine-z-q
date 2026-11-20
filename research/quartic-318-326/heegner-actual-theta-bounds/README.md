# Exact support and input-size bounds for the fixed scalar

For the actual fixed a=0 compact scalar δ and trial q=1,199,923:

- The exhaustive θ scan through 200,000,000 finds only the four previously certified factors. At least one further prime occurs and every further prime exceeds that bound. The **fundamental** discriminant of Q(√(−qδ)) has at least 113 bits.
- A separate 3-adic reconstruction proves at least 207,779 bits for the **raw reduced numerator** of δ. This does not bound the size of the squarefree part at that scale.

The [exact proof with eligibility and exceptions](ACTUAL-THETA-SUPPORT-AND-EXPANDED-INPUT-LOWER-BOUNDS.md) keeps these two statements separate. The [signed independent review](independent/INDEPENDENT-THETA-SUPPORT-AND-HEIGHT-REVIEW.md) includes an independently implemented projective 3-adic point evaluation and a separate continued-fraction calculation. Its review of the 200M sweep checked the eligibility, original code and logs and replayed two bounded segments; it did not independently rerun all 200M inputs.

## Reproduce locally

Requires Python 3, a C++17 compiler and the GMP development headers/libraries. From this directory:

    sha256sum -c SHA256SUMS
    ./replay.sh

The default replay checks the small exceptional place, the four fixed normalizers, the two author height bounds, the byte-identical projective residue, and the independently reconstructed bound. It compiles into a temporary directory and needs no network or outside repo files. Run the following to add the two complete θ intervals (several minutes, machine dependent):

    ./replay.sh --full-scan

The source folder contains exact antecedents for the fixed scalar, original arithmetic and bounded local guards. No full θ support, actual class group, production q₀ qualification, modular coefficient, or Lean theorem is supplied here.
