# Independent native scalar-tower route check

Scope: source-level instance availability for the current isolated FourRootActualOrderGalois318 candidate, not its full formal/source review and not a Lean synthesis claim.

The actual raw carrier is the two-stage K-tensor of the four RootRing factors; RootRing is AdjoinRoot of the actual quadratic polynomial. At pinned Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679, AdjoinRoot has a generic Algebra S instance from Algebra S R, an inherited IsScalarTower R1 R2 instance, and inherited SMulCommClass. Taking R=K, S=P supplies the polynomial action and P/K tower on each root factor. TensorProduct.leftAlgebra preserves that left action, and the native linear TensorProduct.isScalarTower_left (also isScalarTower) supplies its compatibility recursively at both tensor stages. Thus removing a redundant competing P-algebra dictionary is supported by the actual native instance chain, rather than replacing the field carrier or action.

The candidate's base_algebraMap uses IsScalarTower.algebraMap_apply for exactly P,K,L. Its affineTower then connects this native composite to the same original affine embedding using embedding_on_polynomial. No alternate scalar map or branch coordinate is introduced by this route. The actual generic field source and KummerTensorField definitions were read, as were TensorProduct-Basic and Algebra-Tower in Picard's PRIMARY folder. The full candidate review remains owned separately by review_lean.

Supplementary exact native snapshots:
- Mathlib-AdjoinRoot.lean: 51432e606471ffb8331b637394b693b4ddf5214d17182f44556dd182fbd7339d, freshly fetched from the pinned commit.
- Mathlib-TensorProduct-Defs.lean: 03cee05edc34ddcc45d751e910564d020224e618631ff9aa0d7444282ac777d6, copied from the existing pinned tensor research source.

No concrete unsupported instance route found. Elaboration and instance-search behavior remain hosted-test obligations; no local Lean/Lake was run.
