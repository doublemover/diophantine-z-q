# A forced extra discriminant prime for the fixed scalar

The [exact proof note](rc-linked-scalar-norm-pair-dual-hidden-prime-r1/SPLIT-DUAL-AND-FORCED-HIDDEN-DISCRIMINANT-PRIMES.md)
uses the actual split dual elliptic curve of the alternate
fixed-scalar genus-one model. Its rational 2-torsion forces
another odd-valuation discriminant prime \(q>20\,000\,000\)
with \((q/131)=-1\). The proof does not identify \(q\), compute
the exceptional denominator signs, or find a rational point.
The check above 20 million retains the previously published
rank-dependent scope, not a full-scan claim.

The earlier exact local model and bounded support computations
are pinned in the [published local matrix packet](https://github.com/doublemover/diophantine-z-q/tree/527d4f421d526cdbddf0ccd98f27064bf55666a1/research/quartic-318-326/actual-scalar-norm-pair-local-matrix),
whose root manifest has SHA-256
`698da5039087710e46196ed64d265f90af91b76623e4f471619907d13725892a`.
They are referenced rather than duplicated. The only data file
needed to replay the new local check is the unchanged 304-byte
[prime-83 residue](rc-linked-scalar-norm-pair-r1/ACTUAL-ALT-PRIME-83.json)
from that packet, SHA-256
`5b6804fd8617d5a4b250d0f039c27de67a9bf3f558d47a71507be2c699636895`.

The independent cold pass checked the two local x-class
directions, the prime-83 coefficient and point, the exact
forced signs of the hidden product and the bounded conclusion.
It also reproduced the new Python output byte for byte; the
older support scan was not repeated as part of this review.

Replay from this directory with Python 3.10+:

    sha256sum -c SHA256SUMS
    PYTHONDONTWRITEBYTECODE=1 python3 rc-linked-scalar-norm-pair-dual-hidden-prime-r1/check_dual_hidden_prime.py | cmp - rc-linked-scalar-norm-pair-dual-hidden-prime-r1/DUAL-HIDDEN-PRIME.json

This is a proof about the actual compact scalar and finite
local calculation, not a global descent or a Lean build.
