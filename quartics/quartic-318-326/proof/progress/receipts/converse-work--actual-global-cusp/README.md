# Actual modular q*j and global energy to cusp data

Strict kernel PASS: one module, three public theorems and two constructed maps. The exhaustive audit checks 43 declarations including generated record fields and proofs, with only standard roots.

`ActualGlobalCusp318.Data` does not ask for a function G or its analytic properties. Its selected-value field is an equation for `ActualQJ318.jInvariant`, the genuine normalized weight-four Eisenstein series cubed divided by Mathlib's modular discriminant. The data retains actual cusp widths, upper-half-plane points in the fundamental region, holomorphic differential coefficients, global normalized differential-energy measures, exact chart density and non-Weierstrassness.

`Data.toGlobal` constructs the missing G fields from the frozen actual qj producer: G is literally its regularization, its holomorphy and bound128 are proved, G(0)=1 is proved, and its value equation follows from the actual selected j-value. `Data.toCusp` then constructs the exact frozen cusp data, deriving local energy and integrability through the global-energy bridge. No local norm or integrability field is reintroduced.

The averaged actual differential/Wronskian bounds and the quadratic-log Jacobian estimate now consume this concrete data. The width, point, coefficient and measure data are preserved, so no implicit change of chart or averaging field occurs.

The actual complex curve, normalized differential measures, chart interpretation, selected fiber j-values and finite/Arakelov objects still need their geometric realization. This packet removes the abstract-G estimates and local-energy hypotheses from the analytic producer interface; it does not prove the global GeometricRealization existence.

Replay with `bash converse-work/actual-global-cusp/verify.sh`. Every frozen dependency is hash-bound in the receipt. No repository or Git changes were made.
