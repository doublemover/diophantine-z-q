# Actual inverse-image Mayer–Vietoris naturality

This69-source packet copies residue-independence-r2 exactly and adds four modules.
No local Lean compilation was run. Strict hosted checks, recursive axiom auditing
and independent acceptance remain pending. The prior65-source endpoint and the
new statements are proposed proofs until those checks finish.

MayerVietorisCoefficientNaturality318 proves naturality of the original section
boundary under an actual coefficient-sheaf morphism. Both the Ext connecting class
and the terminal-generator comparison are retained. The literal overlap section
map is the morphism component, and its actual cohomology map is Sheaf.H.map.
A surjective-boundary criterion compares whole H1 maps by their boundary values.

InverseImageLocalGenerator318 constructs the actual inverse-image free generator
isomorphism at every open, using the original sheaf adjunction and original section
representations. Both directions are fixed by their section evaluations, not
chosen arbitrarily. It proves compatibility with every actual open restriction
arrow and with coefficient morphisms.

InverseImageLocalCohomology318 uses that generator map, exact inverse-image Ext
functor and original adjunction counit to define the local derived comparison.
It proves that degree zero is the literal identity of direct-image/source sections,
and proves restriction and coefficient naturality in every degree.

InverseImageMayerVietoris318 constructs a morphism from the original source cover's
short exact free-generator sequence to the inverse image of the original target
cover sequence. The actual inverse-image cover is proved exhaustive. The middle
map keeps both summands in order, the first map keeps the finite-minus-infinity
sign, and all four edges use the proven generator restriction compatibility.
Ext-class naturality then proves the genuine local connecting maps commute with
the derived comparison. No boundary compatibility is assumed as a premise.

The global-to-local terminal identification in the earlier source H1 is canonical
but was constructed separately through the integer sheaf. Its coherence with the
new local generator comparison is not yet established here. Consequently this
packet does not yet identify its local comparison at the full open with the
original SourceCohomologyComparison318.comparison, nor identify the original five
quotient pullbacks with the five coordinate lines. That precise terminal alignment
and concrete scheme/chart instantiation are the next joins. The existing source
rank5 and nonvanishing proofs do not license assuming those joins.
