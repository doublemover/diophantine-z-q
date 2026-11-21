# Construct local lifts from the given actual exponential

One selected source-only module, no project baseline. Starting from
the identity chart of the actual target, use precisely the pinned
HasStrictFDerivAt.toOpenPartialHomeomorph and to_localInverse (Mathlib
56a0058, Analysis/Calculus/InverseFunctionTheorem/FDeriv.lean).
The inverse derivative is identity at zero. The source invariant
derivative is read in the centered target chart before the
logarithm is chosen, so local lifts and their derivatives are output.

One lift works on a whole open disk. Its increments near each
point equal the same inverse in the recentered identity chart, so
the stated derivative holds at every point of that actual disk.
No new Jacobian group, topological covering lift, period-zero
hypothesis, or assumed derivative of a lift.
