# Genuine proper finite-fiber j and finite arithmetic comparison

This packet strengthens the global surjectivity result with derived properness and finiteness.

- Identify finite-j inverse images inside the open modular quotient with their actual images in the all-cusp compactification. Since every cusp maps to infinity, compact finite subsets of the j-line have compact inverse images in the open quotient.
- Deduce topological properness of genuine j for levels at least five from actual all-cusp compactness, not an assumed properness hypothesis.
- Use the complex analytic identity theorem and the proved genuine cusp nonconstancy to isolate every equal-j point in the upper half-plane. Pass these isolating neighborhoods through the actual open orbit projection to prove discreteness of every quotient j-fiber, including levels with elliptic stabilizers.
- Construct actual continuous surjective level-forgetting maps for divisibility of levels. Use the map from level 5N to level N to prove compact inverse images and properness at every positive level.
- Combine compactness and discreteness to prove that every genuine quotient j-fiber is finite.
- Apply the exact j-compatibility of the literal arithmetic comparison to prove that its fibers are finite. Together with the already-proved global surjectivity, this gives an actual finite-to-one surjection from the admissible Gamma1(3) quotient to every complex point of the specified full fixed arithmetic algebra.

Finite-to-one does not mean injective. This packet does not prove holomorphic variation of the arithmetic source map, its degree, a global analytic/algebraic isomorphism, a compactified comparison, or a PEL identification. The arithmetic localization parameter N and the fixed torsion order three remain distinct.

Verification: sequential Lean 4.35.0 replay with debug.skipKernelTC=false and exhaustive recursive import-all axiom audit of all public/private/generated declarations, allowing only propext, Classical.choice and Quot.sound. This is author replay against pinned predecessor/Mathlib caches, not independent review or full dependency-closure replay. Hold the exclusive workspace compile lock when running build-all.sh.
