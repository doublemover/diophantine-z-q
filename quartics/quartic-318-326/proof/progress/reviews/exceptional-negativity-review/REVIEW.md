# Independent exceptional-negativity review

Accepted at the stated linear-algebra and geometric-application boundary. I copied the source and exhaustive audit into this isolated directory and rebuilt with debug.skipKernelTC=false. The replay reports seven declarations, all with standard axioms only, and the copied Lean files match the frozen source packet byte for byte.

The proof uses actual positive definiteness of -M, not an assumed inverse-sign property. For z=p-n with disjoint positive and negative supports, the distinct-component nonnegative intersections imply n^T M p>=0. From Mz<=0 follows n^T M n>=n^T M p>=0. Negative definiteness forces n=0. The outside-component contribution is separately shown nonnegative before the canonical coefficient conclusion, so no exceptional-support hypothesis is silently lost.

This closes the finite linear-algebra sign step only. The arithmetic surface, minimal regular resolution, actual negative-definite exceptional intersection matrix, distinct-component positivity and adjunction inequality remain geometric application inputs. In particular, it is not by itself FiveContact49Height.
