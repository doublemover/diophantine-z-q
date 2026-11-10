# WITHDRAWN: awaiting corrected include/doccomment syntax

This old binding is superseded and must NOT be used for source clearance or publication. See syntax correction below.

# Independent targeted height scope review

Reviewer resume_pel_order; source review only, no local Lean.

- height-original-metric-assembly-r16: APPLICATION SHA256 `3ffed93eea5ba282b81e2d3a584804981e905ce9371e380ebd23e98b5efd281c`; changed sources: ['IntegralUnitPairNorm318.lean', 'ContactFinitePlaceBaseMap318.lean', 'IntegralValuativeInfinityExtension318.lean', 'IntegralOriginalPairGenerators318.lean'].
- height-normalized-valuative-center-r15: APPLICATION SHA256 `8fe1d86c5bcfc5d280c80b3649a1f3ea56be4e93830d9da74131e69622c0ed70`; changed sources: ['IntegralValuativeInfinityExtension318.lean'].

Verified both SCOPE_REPAIR.json before/after hashes and that no other Lean source differs. Read the complete four changed modules and their theorem consumers. The nine targeted includes expose precisely the proof-only hypotheses: hφ for integral coefficient norm bounds (four lemmas), hv for denominator/separation units (two), hN for local branch/infinity generators (two), ht for infinity point extension (one). Existing callers already supply those arguments. Data-dependent hypotheses already appearing in map definitions/statements remain untouched; no broad section-wide include imposes new requirements on independent lemmas. The normalized-valuative successor repeats only the same infinity-point include. No theorem body, mathematical conclusion, map, coefficient or integrality condition changed. Both canonical static validators pass. Source-level clearance for these narrow scope repairs.

## Superseding syntax correction

After this source review, the integrator supplied a hosted diagnostic proving that an `include ... in` placed between an attached doccomment and its theorem is invalid syntax in this Lean version. Therefore the bound r16/r15 packets above are NOT cleared as compilation-ready. The mathematical hypothesis selections remain correct, but those includes must move before their attached doccomments in immutable successors. This report does not authorize treating the old syntax as accepted. Await corrected successor hashes for rebinding.
