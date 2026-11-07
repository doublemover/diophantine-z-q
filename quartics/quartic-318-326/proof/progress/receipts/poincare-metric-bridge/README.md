# Actual Poincare metric and bicanonical transition

Strict kernel PASS: three modules,25 recursively audited declarations. Standard axioms only; all modules freshly rebuilt with debug.skipKernelTC=false.

`PoincareCurvature318` defines the actual upper-half-plane metric coefficient1/(Im tau)^2 and its translated real-coordinate function. It proves positivity, local C2 regularity and the actual conformal curvature−1 by differentiating the logarithm twice. The exact cotangent normalization2/sqrt(h)=2Im tau is also proved.

`PoincareInvariance318` uses Mathlib's genuine upper-half-plane GL2(R) action and its actual complex derivative. For every positive-determinant real invertible matrix, the coefficient at g*tau multiplied by the norm square of that derivative equals the original coefficient. The determinant-one real subgroup is an explicit corollary. No invariance premise or arbitrary assigned Jacobian is used.

`PeterssonTransition318` proves that the bicanonical coefficient transformation q↦q*(g')² preserves the coordinate norm. It also binds that norm exactly to|q|*(2Im tau)². This preserves the factor four relevant to the section-height producer.

## Scope

These are actual uniformizing-coordinate and real fractional-linear transition theorems. The compact geometric curve, atlas/quotient and its descent, and identification with Yuan's Petersson line remain explicit geometric constructions. The packet does not silently identify an arbitrary source t-coordinate with the uniformizing tau-coordinate or prove the curvature of arbitrary holomorphic pullbacks. That broader local pullback producer is a separate continuation.

Replay with `bash poincare-metric-bridge/build-all.sh`. Dependency/source hashes and exact counts are recorded in receipt.json. No repository or Git changes were made.
