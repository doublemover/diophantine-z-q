# Effective size barriers for the protected original detector CM calculation

On the existing cleared linear key, after protecting both 13 and 19, each of the two balanced selected discriminants has absolute value greater than $2.78\cdot10^{179}$. Tatuzawa's explicit one-exception theorem then makes a class-by-class orbit larger than $8\cdot10^{85}$ on at least one arm of *each distinct pair*. For a repeated pair the proof instead gives the bound on at least one of two admissible shared-prime choices. Both statements concern enumeration, not compressed aggregate methods. There is no actual numerical detector, computed coefficient, or rank claim.

- [Exact proof and strict scope](proof/CLEARED-KEY-AND-PAIRED-CM-OUTPUT-FLOOR.md)
- [Independent primary-source and arithmetic review](independent-review/INDEPENDENT-CLEARED-KEY-CM-OUTPUT-FLOOR-REVIEW.md)

Run the exact integer replay:

    cd proof
    sha256sum -c SHA256SUMS
    python3 -B replay_cleared_key_cm_floor.py | cmp - EXACT-CLEARED-KEY-CM-FLOORS.json
