# Independent review: actual etale normalization

Accepted. The exact copied module was independently rebuilt with strict kernel checking, and all six declarations passed recursive axiom audit with only propext, Classical.choice and Quot.sound. Frozen source and dependency hashes were checked; no upstream files were edited.

The key producer does not assume that the cover algebra is already normal or already an integral closure. Over the actual integrally closed base and actual fraction field, every base integral element is in the base. Tensor-product induction therefore identifies the entire image of the smooth integral-closure comparison with the original smooth algebra. The genuine Mathlib smooth-base-change integral-closure theorem supplies surjectivity onto every integral generic-fiber element. Flatness of the smooth algebra and fraction-field injectivity give the required injectivity into its generic fiber. Module-finiteness supplies the reverse integral implication.

For the quadratic unit-root algebra, etaleness and finiteness are imported from the actual constructed AdjoinRoot presentation; the derivative 2*root is a unit because both 2 and the original unit are units. No chosen square root, Henselian hypothesis, or cover-domain assumption is required. The statement remains valid for a split generic fiber, which is important: it identifies an integral closure algebra in a possibly disconnected generic-fiber algebra, not necessarily the ring of integers in a field.

The finite-order variant uses actual integrality transitivity and a compatible algebra map into that generic fiber. It does not silently identify an arbitrary finite algebra with the manuscript's contact order. The DVR wrapper derives the base normality from the actual DVR instance. The concrete contact-order map, its generic-fiber presentation, and geometric local/global realization are explicitly retained downstream.

The official Mathlib Smooth/IntegralClosure source remains unchanged. The author separately rebuilt that pinned module, and this independent replay recursively checks its proof dependencies through each target theorem. No external axiom for smooth normalization is introduced.
