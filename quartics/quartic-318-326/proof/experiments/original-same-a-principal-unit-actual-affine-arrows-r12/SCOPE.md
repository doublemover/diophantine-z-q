# Original same-A principal-unit affine arrows r12

Exact official r11 is 22/25 with 352 audited and all 97 traced baseline
module keys. The old failed ActualConstantAffineCoefficients is now green.
Only PrincipalUnitActualAffineArrows is attempted red; two dependents
are blocked.

Replace the unknown dependent appLE congruence name with the same
local beta already proven in accepted AffineCoordinatePullback:
case on equality of the actual marked scheme morphisms, then rfl.
Qualify the actual left arrow through Scheme.Modules.Hom.app,
exactly as in accepted PushforwardArrows.left_chart. This preserves
c/hc/hframe in the elaborated theorem type and evaluates the same
pointwise section b without introducing a new field or premise.
No right-arrow, import, terminal or new-owner changes. Unchanged 24
source owners (22 passing, two blocked); same scope 25/97 only.
No Poincare recognition or comparison to old KS is claimed.
