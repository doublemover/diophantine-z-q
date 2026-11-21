# A verified local helper cell at 673 for the original slot 190

The exact old \(a=0\) scalar anchor gives a regular triple of literal detector folds at \(t=61\bmod673\). The slot-190 companion is a nonzero square there, and the five contact forms can have square residues while the order-only denominator prime has a nonsquare residue.

This verifies the local cell on the published anchor only. It does not supply a new common source index or literal pole, a global selected \(n\), a Hecke product, or a mark.

- [Proof and exact finite replay](proof/LITERAL-A0-SLOT190-HELPER673-LOCAL-CELL.md)
- [Signed independent review](independent-review/INDEPENDENT-CM192-LITERAL-HELPER673-REVIEW.md)

    (cd proof && python3 -B replay_actual_source_helper673.py | cmp - EXACT-LITERAL-HELPER673.json)
    sha256sum -c SHA256SUMS
