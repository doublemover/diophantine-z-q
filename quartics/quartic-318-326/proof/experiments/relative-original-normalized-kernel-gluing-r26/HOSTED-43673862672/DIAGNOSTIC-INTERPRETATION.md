# Own gluing25 expanded diagnostics

The exact production module still failed4.576s after76 predecessor successes. The three scoped pp.all declarations were diagnostics only. The current1.43MB log retains the native pp.maxSteps5000 ellipses; no claim that every differing argument was printed completely.

Tokenized parenthesis comparison of the three printed Eq terms gives:
- Error1: entire outer Eq carrier identical; LHS has expanded Line.mk on actual side versus named LineSheafPullback.line on expected side. The final simp unfolds originalRestriction AFTER earlier dsimp, reintroducing wrappers. RHS implicit coercion/type arguments contain native Functor.comp on expected side versus nested Functor.obj on actual side.
- Error2: outer Eq carrier and LHS identical; RHS likewise contains composed versus nested functor-object expressions in implicit arguments. This is not evidence that two mathematical maps differ.
- Error3: visible outer carrier uses Scheme.Opens plus SheafedSpace's topology instance on actual side versus expanded TopologicalSpace.Opens/carrier.str on expected side. Later printed terms include ellipses, so no complete unique-cause diagnosis is asserted.

The bounded candidate removes diagnostic scopes, does named wrapper rewriting FIRST on both hypothesis and goal, then dsimp only of the exact exposed LineSheafPullback.line/Functor.comp definitions. The final square also explicitly reduces Scheme.Opens and the exact native topology-instance wrapper displayed in the log. It does not unfold the concrete geometric frames' dependencies, whole-section maps, native pullbackComp/eqToIso internals, or change resource/transparency/kernel settings. This is a new source experiment, not a proven runtime fix.
