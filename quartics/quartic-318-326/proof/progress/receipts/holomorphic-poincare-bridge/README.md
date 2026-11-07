# Actual holomorphic Poincare pullback and uniformizing section bounds

For a genuine holomorphic local map f with Im(f(0))>0 and f'(0) nonzero, the metric coefficient is the actual function
  h(w)=|f'(x+iy)|²/Im(f(x+iy))².
The packet proves its actual conformal curvature is−1. It does not assume harmonicity, a Cauchy–Riemann identity, a gradient bound or a curvature-transformation law.

`HarmonicAxis318` binds Mathlib's actual real-inner-product Laplacian to the exact two-real-axis second derivatives used by the project. The bridge uses the second-derivative composition theorem on actual linear coordinate lines. `ImaginaryGradient318` derives both real partial derivatives of Im f from the actual complex derivative, proving |grad Im f|²=|f'|².

`HolomorphicPoincare318` uses the proved harmonicity of Im f and log|f'| for analytic functions, the actual gradient identity, and the checked real logarithm formula. This gives Delta(log h)=2h and hence K=−1. Actual coefficient positivity and local C2 regularity are also derived. Noncriticality and upper-half-plane membership at the center give the needed neighborhood conditions; no unjustified logarithm rewrite across zeros is made.

`UniformizingSectionBounds318.Data` replaces the prior hyperbolic coefficient, regularity, positivity and curvature fields by actual local uniformizing maps and their genuine analyticity, noncriticality and upper-half-plane values. The final `integral_section_norms` composes with the actual source metric, compact maximum principle and literal section coefficients to derive the two J²*(4C) archimedean bounds. No metric curvature, derivative-norm identity or section-norm estimate remains as an input.

## Remaining scope

The actual compact geometric curve, choice and gluing of source charts, existence/realization of the local uniformizing maps, and positive continuous global ratio are explicit geometric data. The Yuan Petersson/global line-frame identification and arithmetic section extension remain separate geometric inputs. The constructor is not a proof that the global realization exists, and it does not assert FiveContact49Height unconditionally.

## Reproduction

Run `bash holomorphic-poincare-bridge/build-all.sh`. All modules are freshly rebuilt with debug.skipKernelTC=false and all declarations recursively checked against propext, Classical.choice and Quot.sound only. The pinned official Mathlib cache needed one additional file, Analysis/Calculus/IteratedDeriv/FaaDiBruno.lean, retrieved from the standard cache for the unchanged revision. No repository or Git changes were made.
