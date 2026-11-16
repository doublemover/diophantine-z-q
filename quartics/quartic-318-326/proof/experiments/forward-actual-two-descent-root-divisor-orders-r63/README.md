# Explicit trace parameters in the arithmetic denominator proof

Fresh119 run43915657076 passed118 modules and recursively audited4176 declarations. ThreeDetectorArithmetic318 exceeded the unchanged1,000,000-heartbeat cap at whnf while processing stored_square_denominators. The log also contains a line70 letI linter warning, but this does not causally localize the expensive reduction.

The sole change replaces the final scaled_trace_unit call's three metavariables with its exact assignment, scale and rational parameter. This avoids inferring them through the deeply computed leaves(view ...) expressions. It is a targeted elaboration hypothesis, not a confirmed performance repair. All proof logic, public signatures, hypotheses, imports, options and resource limits remain unchanged.

All1324 other sources and1325-root order remain exact, including118 checked predecessors, the accepted11-root pure chain and the p-adic anchor repair. The next target remains119 roots. No local Lean, new mathematical layer or fullpacket claim; strict hosted checking and recursive audit are required. In particular the explicit local-global input and four actual realization inputs are not discharged.
