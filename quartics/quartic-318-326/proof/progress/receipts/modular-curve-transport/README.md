# Actual modular Weierstrass transport

Status: strict-kernel PASS, 55 declarations in 3 modules, including 13 public theorems. Only `propext`, `Classical.choice`, and `Quot.sound` occur in the recursively collected axiom sets. Lean 4.35.0 and the existing pinned Mathlib revision are unchanged.

## Actual objects and direction

The models are the already constructed genuine normalized complex Weierstrass curves

    E_tau: y^2 = x^3 - E4(tau)*x/48 - E6(tau)/864.

For gamma in the actual image of SL2(Z) and j = c*tau+d, the proved transformation is E4(gamma*tau)=j^4 E4(tau), and similarly weight six. `ModularCurveChange318.curve_change` proves equality of actual Weierstrass models under Mathlib's `VariableChange` action. The unit in that variable change is **j inverse**, because the action rescales coefficients by u inverse to the fourth and sixth powers. `sl_curve_change` specializes directly to every actual SL2(Z) matrix, with no transformation-law premise.

The old-to-new coordinate map is

    (x,y) -> (j^2*x,j^3*y).

`ModularPointTransport318.equation_scale` proves that the actual equation residual scales by j^6. `pointEquiv` and `slPointEquiv` are actual equivalences of the nonsingular Mathlib point sets, including the point at infinity, with explicit inverse coordinate division. Nonsingularity is obtained from the already proved nonzero modular discriminant, not assumed for the target.

This point-set equivalence is not yet packaged as an additive equivalence. Compatibility with the genuine torus parametrization, level-N torsion coordinates, the specified modular family, and point-level versus mu_N moduli conventions remain separate tasks.

## Actual differential calculation

`ModularDifferential318.differential_scale` uses a genuine complex-linear derivation on an arbitrary complex function field. Such a derivation annihilates j, and it proves

    D(j^2*x)/(2*j^3*y) = j^(-1)*D(x)/(2*y).

`modular_differential_weight` and `modular_quadratic_differential_weight` give weights minus one and minus two. This is the pullback under the **old-to-new point map**; it is not the opposite coordinate-substitution convention.

`curve_polynomialY` identifies 2*y with the actual partial derivative in Y of the genuine curve polynomial. `analytic_differential_pullback` proves the identical result for the actual complex derivative along an analytic coordinate parametrization, on the y nonzero chart. Thus neither a derivative transformation rule nor a supplied differential-weight hypothesis is used.

The generic field identity uses totalized division and also holds algebraically at y=0. The analytic differential interpretation is explicitly restricted to the y nonzero chart. A global algebraic differential sheaf, extension across that chart boundary, compact modular quotient, level structure, and arithmetic model are not constructed by this packet.

## Replay

From this directory's parent, run `bash modular-curve-transport/build-all.sh`. Every module is rebuilt with `-Ddebug.skipKernelTC=false`; the final audit includes private and generated declarations. Source hashes, dependency receipts, commands, and exact boundaries are recorded in `receipt.json`. No Git or repository files were changed.
