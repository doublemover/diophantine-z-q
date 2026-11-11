# Actual candidate simple complex fibers

This reconstruction transfers the simple-root fiber count from the monogenic order to the WHOLE original localized candidate order, using the independently reviewed original coefficient-preserving ring equivalence in `pel-original-monogenic-order-r1`.

`BasePreservingAffinePoints318` defines actual ring evaluations and actual Spec(C)-valued scheme points over a specified base evaluation, proves their equivalence by full faithfulness of Spec, and transports every such point in both directions along the actual monogenic ring equivalence. The original regular primitive coordinate is the root coordinate. There is no analytic-image predicate in these point types.

`PELOriginalCandidateSimpleFibers318.produced_candidate_fibers` produces a nonzero polynomial base open, retains the same primitive equation, and proves that every entire original candidate fiber over every complex vector in that open has cardinality equal to the original generic field degree. The derivative of that same specialized equation is nonzero at the primitive coordinate of every original-order evaluation in the fiber. This is now a candidate-fiber statement rather than only an auxiliary monogenic-order count.

All base maps are the original `Localization.awayMap` of the original two projected coordinates. Scheme points are quantified by their exact composition with Spec of that map. Both inverse point transports are constructed, not inferred from equality of cardinalities or from a subset of known analytic points.

Remaining: independent topology on all candidate complex points, original analytic-image local reconstruction, selected-sheet clopenness/exhaustion, continuation/density, whole-image equality, and later rational/PEL/Jacobian joins. No such conclusion is inferred from the finite fiber count.

Status: source draft pending independent review and hosted Lean checking. No local Lean compilation, replay or profiling. Static dependency/source checks do not certify elaboration or the global theorem.
