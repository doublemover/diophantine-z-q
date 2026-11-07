# Verified arithmetic and optimization components

This consolidated stable package contains 50 Lean modules and 300 audited theorem declarations. It includes the local algebra, input integrality bridges, exact logarithm/Padé identities, global and actual-domain nonvanishing results, and the discrete-valuation norm-chain mechanism used by the optimized quartic construction.

The valuation results use Mathlib's actual additive valuations, derive intrinsic even valuation from the reciprocal curve, handle zero leaves, prove arbitrary-length chain noncancellation and exact valuation recursion, and extract every required leaf order from the terminal threshold. The trace-selection and finite Padé-error valuations are also checked.

The complete concrete polynomial bundles are separate. This package does not prove the global elliptic, pole-completeness or prime-selection characterization of the source. The precise remaining arithmetic hypotheses are listed in `arithmetic-obligations.md`.

Use the pinned official Lean and Mathlib manifests, obtain the official dependency cache, then run `bash verify_components.sh`. The script checks source hashes, rebuilds each local module with kernel checking enabled and audits every theorem against only propext, Classical.choice and Quot.sound. No build products or dependency caches are included.
