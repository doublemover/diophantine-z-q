# Bounded external logarithm library check

Read-only GitHub inspection of MichaelStollBayreuth/EllipticCurves main on 2026-11-07. No external source from this library has been imported or executed in this packet.

The fetched lake-manifest.json pins Mathlib exactly to 56a005855ea17e0b0958f73ec801ae140b0a1679, inputRev v4.35.0, matching the current project. Paths require the leading EllipticCurves directory.

- EllipticCurves/WeierstrassFormalGroup/Filtration.lean: formalPoint_add and exists_formalPoint_eq_some are actual point/group theorems, including identity, inverse and tangent branches. Their ambient field is a HeightOneSpectrum.adicCompletion of the fraction field of a Dedekind domain, with an integral Weierstrass model and ellipticity. They are not already stated for our arbitrary WithAbs completion.
- EllipticCurves/Mathlib/Chabauty/LogIso.lean: log_addHom and evalT_scaledLog_add cover the full pO domain, hence normalized depth one, using a complete adic local integral ring O, characteristic-zero field K, injective O→K, and maximalIdeal O=span{p}. The scaled formal-log coefficient binding is built into the resulting package. The corresponding injectivity theorem additionally excludes p=2.
- EllipticCurves/Mathlib/AdicFormalGroupLog.lean generalizes the scaling parameter and supplies complete-adic-local-field machinery. Its completion specializations again require the Dedekind/height-one setup.

This is a promising compatible library, not a drop-in proof of the current source theorem. Either identify our actual integral ring with its local/adic/maximal-ideal interfaces and its formal logarithm with the required H primitive, or complete the current normed restricted-series route. The analytic worker chose the latter because its coefficient, formal addition and actual group bindings are already proved.

Sources:
https://github.com/MichaelStollBayreuth/EllipticCurves/blob/main/lake-manifest.json
https://github.com/MichaelStollBayreuth/EllipticCurves/blob/main/EllipticCurves/WeierstrassFormalGroup/Filtration.lean
https://github.com/MichaelStollBayreuth/EllipticCurves/blob/main/EllipticCurves/Mathlib/Chabauty/LogIso.lean
https://github.com/MichaelStollBayreuth/EllipticCurves/blob/main/EllipticCurves/Mathlib/AdicFormalGroupLog.lean
