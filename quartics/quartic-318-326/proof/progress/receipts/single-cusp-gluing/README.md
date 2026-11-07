# Genuine single-cusp topological gluing

Fresh strict-kernel replay checks all 63 declarations in three modules, allowing only propext, Classical.choice and Quot.sound.

`TwoChartGluing318` constructs actual TopCat.GlueData from an open partial homeomorphism. Its overlap transitions and cocycle are proved, both original spaces embed openly, the exact cross-identification relation is proved, and the two embeddings jointly cover the actual glued space.

`ActualSingleCusp318` applies this construction to the genuine Gamma1 infinity-cusp chart and the actual filled disc. `overlap_source` is exactly the existing quotient cusp neighborhood; `overlap_target` is exactly the disc minus zero. The old quotient and disc embed openly in the actual glued space. `range_original` proves that exactly one new point has been attached, and `cusp_in_open_disc` gives its genuine open disc neighborhood. `SingleCuspDensity318.original_dense` proves the old quotient dense in this attachment.

This is not a set tagged as a compactification: the topology and open embeddings come from genuine TopCat gluing. It is, however, only a topological single-cusp attachment at this stage. Hausdorffness, an extended complex atlas, whole-cusp compactification, and the specified algebraic/arithmetic/PEL model comparison are not asserted by this packet. In particular, generic gluing can be non-Hausdorff; that issue must be checked for this actual attachment rather than assumed.
