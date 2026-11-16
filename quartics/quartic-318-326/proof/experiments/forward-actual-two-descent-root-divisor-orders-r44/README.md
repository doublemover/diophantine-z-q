# Native natural-scalar rewrite orientation repair

Fresh hosted descent40 compilation exposed the exact multiplication-order issue in iterate_transition. Pinned Mathlib Monoid.lean confirms that mul_nsmul gives n • (m • x), while mul_nsmul-prime gives m • (n • x). This successor corrects the bounded-tower iteration, bounded-coordinate modulo annihilation, and Pruefer scalar formula accordingly.

Three proof-body corrections only, no statements, assumptions, imports, typeclass instances, carriers or definitions changed. All1314 other predecessor source bytes are identical. No local Lean, no claimed hosted acceptance; unrelated actual anchor and analytic converse obligations remain.
