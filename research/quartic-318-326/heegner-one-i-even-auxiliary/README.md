# Exact even auxiliary on the historical one-I base

This verifies a full 2-Selmer calculation and a Cassels pairing on the fixed
rational elliptic curve with quadratic-twist parameter
`−489443591 × 2811626664334219040035976315`.
The auxiliary field splits the base bad places and is inert at 53. The exact
pairing proves rational rank zero and 2-primary Tate–Shafarevich group
`(Z/2)²`, without an initial finiteness assumption.
The resulting nonvanishing of the central L-value uses Theorem A of the
external Burungale–Tian rank-zero 2-converse preprint. It is not a mod-13
evaluation, does not prove a nonzero odd coefficient or derivative, and does
not decide the marked base point or the unknown selected companion.

The original [proof and scope](source/ACTUAL-ONE-I-EVEN-CASSELSEL.md) and the
[independent review](independent-review/INDEPENDENT-REVIEW.md) are included as
unchanged source bytes. Both checkers need only standard Python 3.

```sh
sha256sum -c SHA256SUMS
python3 -B source/check_even_auxiliary.py | cmp - source/EXACT-REPLAY.json
python3 -B independent-review/check_even_independent.py source/EXACT-EVEN-AUXILIARY.json \
  | cmp - independent-review/INDEPENDENT-REPLAY.txt
```
