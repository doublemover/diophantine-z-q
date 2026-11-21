# Exact TZ mean replay r5: 4 directly diagnosed proof owners

Predecessor source intake 6d2ccf06c29e090b433f48e1745e324b68f01fee9c090306d20d07a4fbce8e85.
Observed exact run 44856608606: 29/39 compiled, 460 declarations
audited, four direct errors, six blocked, 91 unselected. The raw log
and source hashes for all four owners are checked. Other 126 Lean files
unchanged byte for byte; all imported module-name sets and selected 39
ordered names are identical. No Lean or GitHub operation by this author.

- CanonicalCellRange: the true lower and upper endpoints use explicit
  typed Int comparisons; private Window.coord body is imported only in
  the proof, through an already existing public module edge. The fibre
  sum declares the necessary inferred DecidableEq instance for the
  Pi Fintype; both exact callers already have this instance.
- GlobalCubeAnchor: the two endpoint and one vertex Equiv applications
  are named with their exact pointwise coordinates before the four
  sign cases. Normalize false=true at zero; do not unfold local H
  after congr has already reduced it.
- PhysicalShortZero: carry the entire existing NNRat sum to Real first,
  then split the actual eval-zero test once per summand to match the
  explicit classical Decidable used by the clipping API. Same grid,
  mass, zero criterion and interval terms, no independence added.
- SignedGridPushforward: handle exact stuck if True in the selected
  singleton fibre term with ite_true, no rewrite to inverse products.

No target claim beyond a source-only exact diagnostic successor.
