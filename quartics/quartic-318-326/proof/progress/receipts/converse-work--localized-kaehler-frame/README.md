# Actual Kähler frames in prime-localized Weierstrass charts

Two modules, 13 public theorems, six constructed frames/derivations, and 53
exhaustively audited declarations pass strict kernel checking and the
standard-axiom audit.

`LocalizedKaehlerFrame318.etaleFrame` uses the actual formally-etale Kähler
base-change equivalence, the tensor base change of the given frame and the
canonical tensor-unit equivalence. Exact compatibility is proved on every
mapped universal differential, not merely on an unspecified generator.
`localFrame` derives the required formal etaleness from actual localization.
Normalization of a coordinate differential is preserved, and the normalized
differential is proved to generate the actual localized Kähler module.

`WeierstrassPrimeFrames318` applies this to the actual prime localizations of
both finite Jacobian charts and the infinity Jacobian chart. It constructs
actual frames, proves the dx/dy normalization, and defines genuine relative
local derivations. The local derivations agree with the actual chart
derivations on every element mapped from the chart. No local rank/frame,
compatibility or derivative-preservation conclusion is supplied.

The exact retained boundary is source realization: these are relative
Weierstrass-family differential modules and their actual coordinate-ring
prime localizations. Identification with scheme stalks, completion or another
source local model needs its actual algebra-map compatibility; identification
with a compact modular/PEL base cotangent or bicanonical sheaf is not asserted.
A localization at an arbitrary prime is not silently declared a DVR or a
regular-surface local ring. No global geometric realization is concluded.

Replay `bash verify.sh`. Lean 4.35.0, Mathlib
56a005855ea17e0b0958f73ec801ae140b0a1679, debug.skipKernelTC=false.
All earlier frozen packets and repository/Git files were left unchanged.
