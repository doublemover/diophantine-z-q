# An alternate genus-one model for the exact original scalar

This proof note studies the already-materialized original $a=0$
scalar of the 318/326 construction, with
$h=473592745039516333133760$. It does not change the exact $J$,
scalar $W$, or resulting rational $b$. The new curve is
everywhere locally soluble; a rational point would give the existing
literal `PointPair b`. No rational point, general four-coefficient
witness, or final 318/326 theorem is proved here.

* [Exact two-quadric model, arithmetic proof, and conditional transport](rc-linked-scalar-norm-pair-r1/ALTERNATE-NORM-PAIR-GENUS-ONE-ROUTE.md)
* [Exact critical-prime replay at 83](rc-linked-scalar-norm-pair-r1/ACTUAL-ALT-PRIME-83.json)

An independent pass checked the disjoint-branch and common-branch
local arguments, the signed Jacobian identification and rational
$x$-class, and the orientation and scale in the literal point
transport. The known torsion point's class $3\beta\delta$ differs
from the required class $3\beta$, because the same actual scalar
has $v_{131}(\delta)=1$.

## Replay

From this directory, using Python 3.10 or newer and the standard
library only:

    sha256sum -c SHA256SUMS
    PYTHONDONTWRITEBYTECODE=1 python3 rc-linked-scalar-norm-pair-r1/check_alt_critical_prime.py | cmp - rc-linked-scalar-norm-pair-r1/ACTUAL-ALT-PRIME-83.json

The checker imports the unchanged inert prime-square helper at
`rc-linked-scalar-higher-descent-r1/check_materialized_xi_new_primes.py`.
That helper in turn uses the unchanged
`rc-linked-scalar-specialization-r1/check_actual_scalar_modular.py`
and `rc-linked-scalar-specialization-r1/select_scalar_specialization.py`,
both byte-identical to the published fixed-scalar snapshot at
`e2ef09a`. These sibling directories preserve the original relative
imports. Stdout from the helpers is suppressed by the critical-prime
checker; the compared JSON contains only the exact prime-83 result.
No network, expanded huge rational, external package, or Lean run
is required for this replay.
