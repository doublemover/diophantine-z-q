# Residual Frobenius freedom in the original Gaussian prime selection

The author proof gives a free choice of determinant-one mod-3 Frobenius
class at each distinct prime form of the original detector construction.
It keeps the same original shared-index CRT and Ready outputs. It also
identifies why this freedom does not supply a mod-3 Heegner transfer
between distinct exact twists.

No actual prime key, Heegner phase, trace, rank, rational marked point,
scalar anchor, or four-pole witness is supplied. Auxiliary-prime
indivisibility, toy traces, and unrelated receiver work are not bundled.
This is a paper proof with exact finite arithmetic controls, not a
claim about a new Lean build.

- [Exact author proof](author/GAUSSIAN-PRIMES-AND-THE-ACTUAL-MOD3-TRANSFER-BOUNDARY.md)
- [Signed independent audit](independent-review/INDEPENDENT-GAUSSIAN-MOD3-FROBENIUS-REVIEW.md)
- Check all bytes: sha256sum -c SHA256SUMS
- From author/: python3 -B replay_mod3_groups.py | cmp - EXACT-MOD3-FROBENIUS-CONTROLS.json
