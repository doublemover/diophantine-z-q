# Actual local L² Wronskian estimate

Status: six modules, 55 recursively audited declarations; fresh replay with `debug.skipKernelTC=false`. Every axiom dependency is one of `propext`, `Classical.choice`, and `Quot.sound`.

## Proved analytic endpoint

`ActualWronskian318.local_wronskian_bound` proves

    log ‖det ((iteratedDeriv j f_i b) / j!)‖ ≤ 100 g² log(2 g N)

for g >= 1, N >= 1, rho >= exp(-21)/N, actual functions f_i holomorphic on the open complex disc ball(b,rho), and finite ordinary area energy integral of |f_i|² at most one. It does not assume a coefficient estimate, Wronskian estimate, Cauchy estimate, or determinant-size bound.

`ActualWronskian318.local_coefficient` proves the sharp estimate

    ‖(iteratedDeriv j f b)/j!‖ ≤ sqrt((j+1)/pi) rho^(-j-1).

## Complete proof chain

- CircleEnergy318: actual Cauchy derivative formula, triangle inequality, and integrated variance give boundary coefficient energy. Periodicity supplies the symmetric angular interval.
- DiskEnergy318: actual two-dimensional Lebesgue integration in polar coordinates, including the radial Jacobian, proves the exact radial energy coefficient pi R^(2j+2)/(j+1).
- HolomorphicDisk318: integrates on every smaller closed disc and passes to the open-disc radius by continuity. Finite area integrability and energy <= 1 yield the sharp coefficient bound.
- ActualWronskian318: translation invariance binds the centered integral to the actual disc ball(b,rho).
- WronskianCoefficient318: the literal exp(-21)/N radius gives a uniform coefficient bound.
- WronskianFinite318: the actual matrix determinant's Leibniz expansion gives the required logarithmic estimate. The zero determinant case is included; nonvanishing is not needed for this inequality.

## Normalization and remaining scope

Javanpeykar 2014 defines the inner product as (i/2) integral omega wedge conjugate(eta), and the Wronskian matrix entries as f_k^(l-1)/(l-1)!. In a local coordinate, (i/2) omega wedge conjugate(omega) is exactly |f|² dx dy. There is no extra genus factor in the area energy of an individual normalized differential. The source was independently checked at `five-contact-metric/javanpeykar-2014.txt`, around lines223 and290–325.

This packet proves the local analytic theorem. It does not construct the global modular curve, an embedded holomorphic chart, an orthonormal basis of global differentials, or the global-to-chart measure identification. Those geometric producers must supply the explicit holomorphicity and disc-energy hypotheses. It does not prove `ContactHeight318.FiveContact49Height` as a whole.

`bash build-all.sh` replays all six modules and the exhaustive audit. The manifest pins Mathlib commit56a005855ea17e0b0958f73ec801ae140b0a1679 under Lean4.35.0. The runner uses the existing verified assistant-workspace toolchain/cache.
