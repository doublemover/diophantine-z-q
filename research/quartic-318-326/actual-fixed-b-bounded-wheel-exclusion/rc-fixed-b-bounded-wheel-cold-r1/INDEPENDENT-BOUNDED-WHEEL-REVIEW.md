# Independent cold review: exhaustive bounded fixed-b integer-u wheel

**PASS for the stated bounded ansatz.** Exact author manifest
7f09513184dd3b12897db6a5786519ca8d7864d2dee0d85c620eed5c8bd0d596,
paper 358eb110733c0b86e867263975202af63d85aefa6d408d402e492e202cd6eabd,
arithmetic output
34b59fd33198f03f0d179e177f79cdcad8586704f311840f2151ea7e7445d579.
I checked all manifest members and replayed both exact C++17 and
Python/SymPy outputs byte-for-byte. The downstream exact all17
review binds the distinct scalar and mixed certificates and is
not replaced by this note.

The donor's integer iteration really covers every positive odd
\(u\le8\,000\,000\) prime to 3 and 17, and \(\lambda(u)\) depends
only on \(u^2\). Each unit contact forces nonnegative Legendre
character of \(16u^4+(24+32W_p^2)u^2+1\bmod p\); the 19 denominators
\(32u^2\) are squares at unit \(u\) since \(p\equiv1\bmod8\).
At \(p\mid u\) the necessary test instead passes automatically:
the numerator is 1, so no such input was dropped by the wheel
test. Every omitted possible zero character is recovered from
the exact quadratic in \(u^2\) and both square root lifts, using
the full interval of integer representatives. The resulting five
admissible candidates each have a separate contact with negative
character, so the exact 79 strict outputs exhaust even the weak
nonnegative character condition.

The 62 further local rejections use \(b\) a nonsquare unit at an
odd good place and the identity \(W^2-bY^2=t\) with unit \(t\).
The associated unramified quadratic norm has twice the least
term valuation, forcing \(W,Y\) integral. For a denominator prime
of \(u\), the leading squareclass of \(\lambda(u)\) is that of 2,
and the listed nonsquare 2 prevents a square \(Z^2\). At a collision
prime, \(Z^2-bY^2=\lambda+t\) first needs even valuation; positive
depth additionally forces both \(Y,Z\) to reduce to 0 and hence
\(W^2\equiv t\bmod p\). The exact negative certificate takes a
failure of one of those requirements in each row. The remaining
17 entries are exactly the preceding certified all17 roster.

Therefore there is no rational \(W,Y,Z\) satisfying
\(W^2-1/2399=10568037907556089\,Y^2\) and
\(Z^2-W^2=\lambda(u)\) in all 19 named old balls for any integer
\(u\) with \(0<|u|\le8\,000\,000\) and \(\gcd(u,102)=1\).
This does not cover rational nonintegral \(u\), greater bounds,
relaxed phases or contact balls, other \(b\), the differing
unconditional deep-seed construction, or literal final poles.
No Lean run.

Signed: independent reviewer, 2026-11-21 UTC.
