# Finite auxiliary-coordinate exclusion at the exact scalar index

This follows the exact materialized scalar bundle (commit e2ef09a).
No h, J, label, or scalar coefficient has changed. The local sieve proves
that at this scalar the specific auxiliary chart has no rational k
of height at most 100,000. It is not a bound on the possible height of a
rational point, does not address all two-parameter constructions of a
PointPair, and does not give a global rank or Sha conclusion.

See [the arithmetic argument](FIXED-H-HEIGHT-SIEVE.md) and
[the independent review](INDEPENDENT-FIXED-HEIGHT-SIEVE.md).
The two scalar helper scripts and exact input JSON are copied byte-for-byte
from the original bundle so this directory replays standalone.

## Replay

With Python 3.10+ and standard library only:

    sha256sum -c SHA256SUMS
    PYTHONDONTWRITEBYTECODE=1 python3 check_fixed_h_ray_sieve.py | cmp - FIXED-H-HEIGHT-SIEVE.json
    PYTHONDONTWRITEBYTECODE=1 python3 check_fixed_height_sieve_independent.py
