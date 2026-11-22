# Original fixed-103 and fixed-241 physical index floors

This package contains the exact corrected proof, standard-library arithmetic replay, and the independent signed review. It copies no older dependency: the precise donor manifest identities are listed in `author/SOURCE-IDENTITIES.txt`.

- The bound $|D_i|>2.78\cdot 10^{244}$ is for **both arms in all three slots** of this protected positive linear-key construction.
- The final-anchor bound of more than $2^{103860}$ **bits** is for **slot 190 only**, on the actual final-anchor branch.
- The Tatuzawa consequence is only for an evaluator emitting or visiting each CM class index, with its one possible exception. It is **not** an algorithmic complexity lower bound.
- The source, companion squareclass, and moving signed coefficients remain undetermined.

Exact replay, from this directory:

```sh
sha256sum -c SHA256SUMS
(cd cold && sha256sum -c SHA256SUMS)
(cd author && sha256sum -c SHA256SUMS &&
 python3 -B check_fixed103_241_floor.py | cmp - EXACT-FIXED103-241-FLOORS.json)
```
