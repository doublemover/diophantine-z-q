# TZ39 two-site repair after exact hosted r10

Exact run 44868364366; raw inventory
bcf7a902a0fe3f53995c77b865fb824c8b377431cb443c41f3d28e7f56fa176a;
36/39 checked and 530 declarations audited. Same lone directly
diagnosed owner; both old Context root diagnostics cleared.

- Raw L136: Keep coefficient reduction nonzero as an explicitly typed
  polynomial G on the original coordinate type. Pass the actual
  equality of its renamed image to the forward direction of the pinned
  MvPolynomial.rename_eq_zero_iff_of_injective G ... (Mathlib
  Algebra/MvPolynomial/Rename at 56a00585); contradict the retained
  exact old original-slope marker. This no longer asks simp to find the
  correct polynomial/renaming as a higher-order inference step.
- Raw L163: reduce the cardinal of the exact universal FinSet before
  applying the dependent Fintype.card_fin numeral. No change to the
  retained cell or its ordinary finite carrier.

No import edges, theorem statements, parameters or other Lean bytes
change. Same exact 39 order; all 129 other source files are unchanged.
Static repairs only; not a build result.
