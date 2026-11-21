# Local Abel-sheet pushforward from its complex derivative

Static source only. Takes a genuinely injective coordinate sheet with an actual complex derivative of the given map. Derives exact determinant-square change of variables, rather than assuming one source-pushforward equality per sheet. The real norm of complex scalar multiplication is computed in Mathlib's actual (1,I) basis; norm transitivity identifies it with the real Jacobian of the whole complex-linear derivative. The target and source reference Haar measures here are the same in those coordinate frames. The actual identification of the torus frame/ordinary density with these coordinates and construction of the exhaustive local inverse sheets remain separate.

Pinned Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679:
- LinearAlgebra/Complex/Module: coe_basisOneI, coe_basisOneI_repr.
- RingTheory/Norm/Defs: Algebra.norm_eq_matrix_det; RingTheory/Norm/Transitivity: LinearMap.det_restrictScalars.
- Analysis/Calculus/FDeriv/RestrictScalars: HasFDerivWithinAt.restrictScalars.
- MeasureTheory/Function/Jacobian: map_withDensity_abs_det_fderiv_eq_addHaar.
