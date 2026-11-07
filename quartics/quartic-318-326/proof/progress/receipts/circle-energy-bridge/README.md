# Actual Taylor coefficient circle-energy producer

`CircleEnergy318.coefficient_energy_interior` proves the exact boundary estimate

`norm(iteratedDeriv j f c / j!)^2 * r^(2*j) <= (2*pi)^(-1) * integral[-pi,pi] norm(f(c+r*exp(theta*i)))^2`

from `DifferentiableOn Complex f (Metric.ball c rho)` and `0 < r < rho`. The coefficient is the actual factorial-normalized iterated derivative. There is no supplied coefficient, mean-value, norm or energy estimate.

The proof uses Mathlib's actual Cauchy integral formula for higher derivatives and the norm inequality for the Bochner integral. It proves the required interval Cauchy–Schwarz estimate independently by integrating the nonnegative square about the mean. Exact periodicity moves the circle integral from `[0,2*pi]` to `[-pi,pi]`.

Exports:
- `integral_sq_le`: continuous real function interval variance bound.
- `coefficient`: exact iterated derivative divided by factorial.
- `coefficient_l1`: actual Cauchy coefficient L1 bound on a closed disc.
- `coefficient_energy`: closed-disc energy bound over `[0,2*pi]`.
- `circle_energy_interval`: exact symmetric interval conversion.
- `coefficient_energy_interior`: requested open-disc, interior-radius theorem over `[-pi,pi]` with explicit exponential parametrization.

This supplies the circle step only. Polar/radial integration, global differential L2 normalization, and the geometric atlas remain separate producers. The Wronskian assembly can consume the theorem directly.

Replay with `bash run.sh`. The source was rebuilt with Lean 4.35.0, strict kernel type checking, followed by an exhaustive recursive axiom audit permitting only propext, Classical.choice and Quot.sound. Exact logs and hashes are included. No repository or Git modifications were made.
