# Actual local-unit norm-coercion repair

Fresh strict run44000133379 retained the exact unit-squareclass producer613e3d55 and audit6, but the local-unit consumer failed at its reversed implicit norm_coe rewrite. Replace only that entry with forward PadicInt.norm_coe u, matching the actual norm of the Qp coercion and identifying the argument explicitly.

All1348 other source bytes and the1349-root order remain unchanged. Definitions, hypotheses, options and limits are untouched. Replay is the same two-root closure. No finite assembly or global compatibility layer is added. Source review does not establish that the transparency failure is cured; strict replay remains required.
