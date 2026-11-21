# The same-surface height bound with a +11 offset

The [exact comparison](author/UNCHANGED-METRIC-CURVATURE-64.md)
proves a strict offset below 11 for the same selected quaternionic
abelian surface in the literal 318 and 326 reverse arguments. It does
not change either Hodge tensor or the original test metric. The full
nonnegative curvature numerator is bounded below on 44 exact radial
intervals and one analytic tail; the resulting hyperbolic metric
comparison combines with the unchanged finite divisor.

The [independent signed review](review/INDEPENDENT-ACTUAL-SAME-A-CURVATURE-PLUS11-REVIEW.md)
includes a separate exact integer/rational checker on the stored
interval certificate. The precise finite arithmetic and normalization
come from the [previous +22 publication](https://github.com/doublemover/diophantine-z-q/tree/25f050304eb7e9e124bd899dc8c83699b8edf273/research/quartic-318-326/original-same-a-finite-cluster-gain22).
The key earlier papers and finite calculation are copied verbatim into
the background directory. Neither the earlier +64/+22 constants,
the native +120 endpoint, nor the separate forward proof is changed.
This is reviewed paper work and exact arithmetic replay, not Lean
evidence or a new construction of the underlying surface.

Reproduce with Python 3 and the standard library from this directory:

    sha256sum -c SHA256SUMS
    (cd author && sha256sum -c SHA256SUMS)
    (cd review && sha256sum -c SHA256SUMS)
    python3 author/replay_curvature.py | cmp - author/EXACT-CURVATURE.json
    python3 review/verify_curvature_from_json.py author/EXACT-CURVATURE.json
    python3 background/check_contact_cluster_gain.py | cmp - background/EXACT-SAME-PAIR-CLUSTER-GAIN.json

The original workspace-relative donor path list is retained unchanged
under author. Its two predecessor bytes are present here as
background/SAME-SELECTED-REVERSE-FOR-BOTH-LITERAL-TABLES.md and
background/PRIOR-PUBLICATION-SHA256SUMS.txt; the root checksum binds
the portable copies. The latter is a historical original manifest,
not a manifest for the subset copied into this package.
