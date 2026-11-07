# Actual p-adic elliptic logarithm and source bridge, kernel-checked packet

This packet proves the actual logarithm construction over Q_p for p >= 19 and any D in Q_p with norm(D) <= 1, on the short curve y^2 = x^3 - D*x.

## Proved results

- The actual subgroup of Mathlib elliptic points parametrized by u = p*t, t in Z_p. The domain includes units t (original depth one) and the identity point.
- The full convergent H series with coefficients binomial(2j,j)/(4^j*(4j+1)), its canonical reciprocal branch, and exact compatibility with the actual elliptic group law, including secant, tangent, inverse, and identity branches.
- An actual additive homomorphism logHom on that subgroup. It is injective and exactly preserves the additive valuation of the formal parameter z = -x/y, including the identity's top valuation.
- Actual affine-point membership from explicit curve, nonzero-coordinate, and small-parameter conditions. The local reciprocal chart is constructed; no square root of 1/x is assumed.
- Exact identification of the actual logarithm with z*G(w), w=D/x^2, on the canonical near-one branch, independent of the sign of an external reciprocal chart.
- First-order and Pade precision for the actual logarithm and actual logarithm ratios. The Pade ratio bound is v(zP/zQ)+16*min(r,s), under the explicit zero-or-finite w-depth hypotheses.
- A generic closed-disc evaluation/composition and two-variable pullback theorem for complete ultrametric integral normed rings, with explicit injective coefficient-map bindings. This is reusable infrastructure, not an assertion that every abstract instance is realized.

## Main entry points

ActualLogHom318.formalSubgroup, logHom
ActualLogIsometry318.logHom_injective, logHom_valuation, logHom_difference_norm
ActualLogMembership318.affine_mem
ActualLogIdentification318.logHom_eq_primitive, logHom_z_valuation, logHom_pade_error
ActualLogRatio318.first_order_ratio_precision, pade_ratio_precision
IntegralLine318.evaluated_addition, evaluated_parameter, evaluated_curve, evaluated_ordinate

## Added source interfaces

- SourceLogDomain318 gives actual affine/reciprocal subgroup membership from normalized source valuations, including the identity and either reciprocal ordinate sign.
- ShortCurveBaseChange318 gives the actual additive, injective short-curve base-change map, its coordinate formulas, integer-scalar compatibility, and formal-parameter/argument transport. Source and target DecidableEq instances are explicit.
- ActualJLog318 identifies the actual logarithm with -u*J(v-1) on the explicitly positive reciprocal branch, and proves its 16r Pade and 8r linear precision with zero endpoints.
- JLinear318 supplies the full infinite-series linear approximation used by the exceptional alternate source row.

## Scope

This packet is the split Q_p logarithm construction plus generic evaluation infrastructure. It does not assert that the complete literal source arithmetic equivalence is finished. The actual inert quadratic completion and its logarithm assembly are separate packets. Source-row decoding, global Mordell-Weil/height arguments, and final arithmetic composition remain separate obligations unless independently certified elsewhere.

## Verification

Lean 4.35.0, Mathlib commit 56a005855ea17e0b0958f73ec801ae140b0a1679. Every included project module was rebuilt from its frozen source with debug.skipKernelTC=false. SourceLogBridgeAudit318 recursively audits every declaration of every included project module, including generated private helpers. Only propext, Classical.choice, and Quot.sound are accepted. No sorry, admit, native_decide, unsafe declarations, or custom axioms are used.

Run bash replay.sh with the pinned Lean/Lake toolchain and the Mathlib dependency cache available. Sources, ordered replay, per-module logs, and hashes are included. Binary build products are deliberately not included.
