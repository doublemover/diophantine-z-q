# Exact order-five support exclusion for the fixed quartic scalar

For the previously materialized a=0 scalar, consider a moving prime
outside the support of 2·3·5·7·R·(1+A)·β at which both source reductions
are killed by 5 but at least one is not the identity. No such prime
divides the actual numerator H or alternate discriminant L′. The proof
does not apply to higher orders, mixed orders, or arbitrary source
points. It does not prove a factorization, Selmer statement, rational
point, or Lean theorem.

The original Node scripts, separate Python determinant/division
replay, separate three-candidate elliptic calculation, paper
proof and exact outputs are included unchanged. Run sh replay.sh
with Node.js 18+ and Python 3. Allow several minutes for the exact
80-kilobit modular division sequences; the scripts do not scan prime
intervals. They recompute the whole determinants and compare the
original output bytes and the overlapping numerical invariants.
For only the fast residual elliptic check, use --local-only.

The original scalar data are fixed at the
[materialized scalar specialization](https://github.com/doublemover/diophantine-z-q/tree/e2ef09acc3675847eacda95f084c3ae86396c4b5/research/quartic-318-326/actual-scalar-specialization).
