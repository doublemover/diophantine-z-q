# All oriented valuations at 11 in the bounded fixed-241 CM control

This packet computes the complete 11-supported component of the fixed-241 oriented CM ideal for \(D=-311\). It follows the actual nineteen maximal-order classes, lifts the ordered flags, and evaluates all 4,598 true conductor-241 arcs at both named coefficient places. The two direct exponents are \(-20,+20\); complex conjugation gives the other two. Under the four imaginary quadratic norm projections, only the field of \(\sqrt{-5\cdot241\cdot311}\) has a nontrivial 11-component: exponent \(-80\) at the root \(9\bmod11\) and \(+80\) at its conjugate.

This is a bounded control, not an original detector value. Neither the whole fractional ideal nor a residue at 29 is recovered from this one prime. The earlier two-path diagonal subtotal \(-4\) is valid but its two complete arcs have zero signed contribution after all factors are included.

- [Full proof and quadratic projections](source/high-hom-1120/heegner-compressed-trace/original-D311-inert11-quadratic-projections-r1/EXACT-D311-P11-ALL-PLACES-AND-QUADRATIC-PROJECTIONS.md)
- [Exact rows for both coefficient places](source/high-hom-1120/heegner-compressed-trace/original-D311-inert11-quadratic-projections-r1/EXACT-D311-P11-BOTH-COEFFICIENT-ROWS.ndjson.txt)
- [First-place calculation, precise cycle, and nested witnessed controls](source/high-hom-1120/heegner-compressed-trace/)
- [Independent signed review](independent-review/INDEPENDENT-D311-P11-ALL-PLACES-REVIEW.md)

Run sh verify.sh with Python 3, cmp and sha256sum for hashes, all 4,598 determinant signs in arithmetic, and the two totals and quadratic projections from the exact table. Run sh verify.sh --all, additionally with python-flint 0.9.0, to independently regenerate the full geometry and factor depths in four isolated workers. The original newline-delimited data bytes are stored with a .txt suffix for portability. The verifier restores their original logical filenames in a temporary checked copy; the exact source and donor scripts are unchanged.
