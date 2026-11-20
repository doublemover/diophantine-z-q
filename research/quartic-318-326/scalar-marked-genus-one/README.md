# Original quartic scalar pole: marked auxiliary cut and exact 131 control

This source-only paper supplement studies the actual scalar producer
of the original 318/326 construction. It does not alter the original
polynomial, claim all four rational points, or assert any new Lean
kernel acceptance.

* EXACT-MARKED-QUARTIC-AND-THETA-OBSTRUCTION.md: exact marked
  parametrization, original selector constraints, and why some tempting
  simpler simultaneous constructions miss the required class.
* SCALAR-SAME-THETA-GENUS-ONE-CUT.md: one genuine one-variable cut
  for the same beta and theta; on the literal a=0 support it has
  local points at all places, with the stated real and residue opens.
* THETA-CLASS-ISOGENY-DESCENT.md: identifies the remaining global
  squareclass on the explicit auxiliary curve using its order-four
  point. This is not a rank-only problem.
* NO-GENERIC-MARKED-SECTION.md: no generic beta-marked point on
  the actual nonsquare-theta norm conic in the a=0 case. This
  distinguishes generic function-field rank from a specialized
  arithmetic fibre, where the rank and the marked class can change.
* FINITE-SPECIALIZATION-SELMER-TEST.md: exact finite local
  tests on the models obtained at any one specified c, and the
  limits of the resulting rank bound.
* ACTUAL-A0-THETA-131.md: an actual allowable scalar progression
  at a=0 with theta ramified at 131, retaining the original labels
  and a real admissible index. It does not identify a numerical
  h or the full theta or an ordered Gaussian prime tuple.

Exact finite arithmetic replay (Python 3, standard library only):

    python3 check_actual_131_constants.py > /tmp/actual-a0-theta-131.json
    diff -u ACTUAL-A0-THETA-131-CONSTANTS.json /tmp/actual-a0-theta-131.json

The numerical check proves the displayed residue table, not
existence of a global rational point. The paper proof invokes
the pinned finite scalar-depth, continuity and real-center statements
to realize the arithmetic congruence at an actual index.
