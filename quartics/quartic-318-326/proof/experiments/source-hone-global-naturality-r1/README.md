# Original scheme-H1 pullback and actual boundary naturality

This71-source packet copies geometric-naturality-r1 exactly and adds two modules.
No local Lean build was run. The complete chain remains pending hosted strict
compilation, recursive axiom audit and independent acceptance.

InverseImageTerminalCoherence318 addresses the precise normalization left open
by geometric-naturality-r1. The earlier terminal generatorIso is evaluated through
its actual section representation. The earlier integerIso is evaluated through
its original composed adjunction and leftAdjointUniq. Their section normalizations
agree, so the local generator comparison and inverse-image integer-sheaf comparison
commute, in both hom and inverse directions. The inverse-direction identity is
then used inside the exact Ext comparison. Thus the original global comparison
SourceCohomologyComparison318.comparison is identified with the new local-at-top
comparison in every degree; no alternative global cohomology map replaces it.

SchemeBoundaryNaturality318 combines that equality with the actual short-complex
Ext-class naturality from the prior packet. It proves global boundary naturality
for the original direct-image comparison, then identifies degree-zero local
comparison with literal overlap sections. Finally it composes the actual
StructureAdditiveSheaf318.pullback with the same comparison used in
SchemeSourceCohomology318.pullback. The resulting theorem says precisely that the
original scheme-H1 pullback sends the original boundary of x to the original
boundary of f.app(U intersect V)(x), on the entire inverse-image cover. The
AffineCoverHOnePresentation318 boundary used by the concrete coordinate proof is
identified definitionally in the final theorem. The finite-minus-infinity sign,
original maps and full opens are unchanged.

This is a proposed unconditional naturality theorem for every actual scheme map
and two-open cover. The original five quotient maps are not yet instantiated:
one still must compare their chosen finite/infinity charts with those inverse
images and compute the exact original section pullbacks or normalized traces on
the five concrete source representatives. Source dimension5 and nonzero character
lines alone do not provide those computations. No original quotient decomposition
or target nonvanishing is claimed solely from this naturality packet.
