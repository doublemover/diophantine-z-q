# Literal smooth branch and infinity metric extensions

Strict kernel PASS: three modules, 21 public theorems and 32 recursively audited declarations; only standard axiom roots occur.

The literal source coefficient is (1+sum_i|t−a_i|)/product_i|t−a_i| for the four finite contacts a=(0,32,76832,−343). All contacts and signs are actual complex numerals. Their distinctness is checked.

At a chosen finite branch, translating the branch value to zero splits the four contacts exactly into that branch and the remaining three. The actual pullback by t=a_i+z², using the actual complex derivative2z, is proved on z≠0 to equal

4(1+|z|²+sum_{j≠i}|a_i−a_j+z²|)/product_{j≠i}|a_i−a_j+z²|.

This displayed coefficient is C∞ as a real function at zero and strictly positive there. The squared norm term |z|² is differentiated as a smooth squared norm; no smoothness of |z| at zero is asserted. All other norm arguments are nonzero at the center, and Mathlib's genuine real smoothness of the norm away from zero is used.

At infinity, the exact actual derivative of t=1/z² is−2/z³. The punctured pullback is proved, not merely asymptotically approximated, to equal

4(|z|²+sum_i|1−a_i z²|)/product_i|1−a_i z²|.

This coefficient is C∞ at zero, with exact value16 and hence positive. The sum has exactly four terms, which is used in both the value and cancellation of the norm powers. The pullback equalities are valid for every nonzero z under Mathlib's total division; in their intended chart neighborhoods the other branch factors are nonzero by continuity.

`LiteralMetricExtension318.smooth_axisC2`, `finite_branch_axisC2` and `infinity_axisC2` directly supply the exact two-real-coordinate `AxisC2` input of the conformal-curvature bridge. Thus these are actual analytic producers for the source metric, not a supplied smoothness or positivity property of an abstract coefficient.

## Exact geometric boundary

The actual Shimura covering must still supply its degree-two local coordinates t−a_i=z² and t=z^(−2), and identify the quotient coordinate with these literals. Those model/ramification facts are separately reviewed classical geometric inputs. This packet proves the resulting local analytic extension and exact pullback, not the existence of the curve/charts, hyperbolic uniformization, or the global GeometricRealization.

## Replay

Run `bash converse-work/metric-smooth-extension/verify.sh`. It rebuilds all three modules and their exhaustive audit with `debug.skipKernelTC=false`. Frozen dependencies are hash-bound; no source in a frozen packet, repository, or Git state was changed.
