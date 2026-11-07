# Actual Kähler frames on Weierstrass Jacobian charts

Two modules, 13 public theorems and 10 explicit definitions pass strict kernel
checking. The exhaustive recursive audit covers 58 declarations, including
construction helpers; only the standard axioms occur.

## Actual presentation and frame

`JacobianKaehlerFrame318.localizedPresentation` constructs the genuine
submersive presentation of the actual Jacobian localization of a two-variable,
one-relation algebra. Its variables include the actual inverse-Jacobian
variable, and its two selected variables are that new variable and the
original selected coordinate. The complement is explicitly the other original
coordinate. Mathlib's actual cotangent-complex theorem gives a one-element
basis of the actual Kähler module, proved to be the universal differential of
that remaining coordinate. The resulting explicit linear equivalence sends
that differential to 1, and the same differential is proved to generate the
whole module. Freeness, rank one, a frame and differential generation are not
assumed.

`WeierstrassKaehler318` specializes this to the genuine finite coordinate rings
and infinity equation already constructed in the project. On the D(2y) affine
chart the frame sends dx to 1; on the other affine Jacobian chart it sends dy
to 1. On the actual infinity Jacobian chart it sends dx to 1. The corresponding
differentials generate the actual modules. Their duals are genuine relative
integral derivations, with the coordinate value exactly 1. The literal OpenJ
family inherits the exact frames without an extra rank, basis or smoothness
premise. The proof works over arbitrary commutative base rings, including rings
with zero divisors, since only actual localizations and presentation theorems
are used.

The existing discriminant-unit and infinity-open-cover packets give coverage
by these actual smooth charts. This packet does not repeat or assume their
final smoothness as a replacement for the explicit frame construction.

## Exact remaining interface

These are relative differentials of the actual Weierstrass family over its
stated base. They are not silently identified with the cotangent line of the
compact modular/PEL base curve, nor with its bicanonical sheaf. Transport to
further local rings, normalization or completed charts requires the actual
algebra maps and differential-base-change compatibility. Source coordinate and
canonical-line/metric identifications remain separate. When a chart is an
actual domain and a fraction field is supplied, the prior fraction-derivation
packet can extend the constructed integral derivation without a preservation
premise. No global GeometricRealization is concluded here.

Replay `bash verify.sh`. Lean 4.35.0 and Mathlib revision
56a005855ea17e0b0958f73ec801ae140b0a1679, debug.skipKernelTC=false. No frozen
producer, repository or Git file was changed.
