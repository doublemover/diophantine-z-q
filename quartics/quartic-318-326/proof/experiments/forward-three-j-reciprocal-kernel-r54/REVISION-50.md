# Hosted223 explicit rational target action repair r50

Hosted223 passes the r49 transitivity-kernel proof and stops LocalizedRationalDifferentials318. Its local targetAction instance has uninferable g,u arguments; Lean falls back to the source localization action in later declarations. The target action sends X to g/f, whereas the source action sends X to the source coordinate, so confusing these is mathematically material.

This successor removes the illegal implicit local instance. targetTower now explicitly states and proves a tower under letI targetAlgebra g h u. actual_jacobian and relativePresentation explicitly install the same target algebra in both their statement and body; the latter installs the produced tower before the quotient theorem. The separately defined value and frame still use their original source localization action. The downstream Laurent and reciprocal consumers already specify this same targetAlgebra in their expected types, so all105 other modules remain exact r49 copies.

The repair changes explicit scalar-action binders to encode the intended actual rational target, not the equation, derivative, localization, numerator inverse, coefficient ideal or maps. The exact failure is retained. No heartbeat increase; no local Lean. Independent review and hosted compilation required; global sheaf and full318/326 theorem remain open.
