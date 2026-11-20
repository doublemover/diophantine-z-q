# Reproduce the original scalar squareclass cutoff

This source-only supplement excludes all K≤100,000, where K is
the positive squarefree part of the actual A=114444R at an
integer source input. It does not construct a qualifying pole
or a rational point, assert a minimal attainable K, call Lean,
or depend on the E323 modular computation.

From this directory, run:

    python3 check_small_scalar_squareclasses.py > /tmp/scalar-cutoff.json
    diff -u SMALL-SCALAR-SQUARECLASSES.json /tmp/scalar-cutoff.json

The checker uses only Python's standard library and exact integer
arithmetic. It first verifies the coefficients and bound on
pairwise determinants; it then maps the possible odd valuations
to support masks. It enumerates the finite candidate **squarefree
parts**, not actual integer source inputs. The mask constraints
and successive congruences are only necessary, so a surviving
class would not prove a producer; the empty survivor list rules
out the whole bounded set. Read SCALAR-NONSQUARE.md for the
unbounded hand proof excluding K=1, which needs no checker.

All three payload files are byte-for-byte the independently
cold-reviewed source/evidence. The independent review verified
the four literal factor slopes/constants, all six pairwise
determinant supports, the support-mask necessity and direction,
and the exact 3,522-case zero-survivor replay. This is a paper
and executable-checker result, not Lean kernel acceptance.
