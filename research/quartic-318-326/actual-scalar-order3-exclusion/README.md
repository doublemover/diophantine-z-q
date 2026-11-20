# Exact order-three source exclusion for the actual fixed scalar

On the literal fixed elliptic arithmetic (h,J), there is no moving prime
of the actual numerator (H) or discriminant factor (L') where **both**
indexed source reductions are killed by 3 and at least one is not the
identity. The statement does not exclude moving primes where one of the
two orders is not a divisor of 3, and does not settle the specialized norm,
the denominator phase, a new Selmer class, or global solubility.

The source is the same fixed scalar as the
[archived specialization](https://github.com/doublemover/diophantine-z-q/tree/e2ef09acc3675847eacda95f084c3ae86396c4b5/research/quartic-318-326/actual-scalar-specialization).
The eliminated (H,L') are the ones in the
[alternate norm-pair proof](https://github.com/doublemover/diophantine-z-q/blob/527d4f421d526cdbddf0ccd98f27064bf55666a1/research/quartic-318-326/actual-scalar-norm-pair-local-matrix/rc-linked-scalar-norm-pair-r1/ALTERNATE-NORM-PAIR-GENUS-ONE-ROUTE.md).
All files here are published as exact proof/replay source, not Lean or a
whole explicit factorization.

- [The completed exclusion](rc-linked-scalar-order3-resultant-gcd-r1/EXACT-LITERAL-ORDER3-RESULTANT-EXCLUSION.md) uses a single normalized division-polynomial coefficient pair at 3h modulo each whole resultant. It compares each with the corresponding h-pair; all resulting prime factors already make both h-branches identity.
- [The original eliminant](rc-linked-scalar-order3-resultant-r1/FIXED-DEGREE-ORDER3-ELIMINANTS-ON-ACTUAL-H-L.md), code, and exact JSON are retained byte for byte. Its earlier partial factor screen is not needed for the completed exclusion.
- [Independent review](independent-review/INDEPENDENT-REVIEW.md) includes a separate Newton-sum construction and multiplication-norm determinant replay for both whole resultants.

From this directory run `sh replay.sh`. This uses only the Python standard library.
The auxiliary author's original eliminant construction also replays with
SymPy if desired, but that extra dependency is not needed for the independent construction.
