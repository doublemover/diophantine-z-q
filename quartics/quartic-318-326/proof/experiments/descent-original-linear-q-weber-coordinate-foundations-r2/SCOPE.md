# Exact reciprocal pole repair; the parallel degree-one scope is unchanged

Official r1 selected only the five-module reciprocal pole branch:
4/5 compiled, 59 standard declaration audits, no baseline or reuse.
The sole failing application at line 93 passed the membership proof
as the first element argument of ValuationSubring.mul_mem. Supply
both explicit element slots. This is the same form already used by
the strict HenselianPointMap donor. No change to theorem statements,
polynomial evaluations, valuation, assumptions or imports.

All seven peers are byte-exact, including the independent and
unselected 3/0 residual degree-one branch. Both old separate
selector scopes are preserved. Select only the desired branch,
not a combined broad packet. No new Lean success asserted.
