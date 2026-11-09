# Concrete independent normalizing radicals

This is a new, bounded algebraic prerequisite under investigation. It is not a proof of real orbit density, a construction of the actual identity component, or a replacement for the historical component/scalar argument. Hosted Lean checking and distinct source review are pending. No local Lean compilation was run.

## Actual objects

The source coefficient is D = (3 - sqrt(2))^2 in K = Q(sqrt(2)). Define delta = 3 - sqrt(2) and deltaBar = 3 + sqrt(2). Both have rational norm 7 and their product is 7.

The module proves that 7 and 14 are not squares in Q by descending a rational square of an integer through the existing integral-closure theorem to an integer square and excluding the finite integer possibilities. The quadratic square-reflection theorem then shows that 7 is not a square in K. Taking rational norms excludes squares of delta and deltaBar in K. The same quadratic square-reflection theorem shows that deltaBar stays nonsquare in K(sqrt(delta)): its only possible square classes would be deltaBar or delta*deltaBar = 7.

Consequently the literal iterated QuadraticAlgebra construction is a field of degree four over K. It contains both specified roots and an actual algebra automorphism over the first extension fixing the first root and negating the second. The first root squares to delta; the second squares to deltaBar, with explicit algebra maps at both stages. This is an algebraic sign operation, not a pointwise choice of real square roots.

## Intended next comparison, not proved here

Multiplying each real coherent u coordinate by sqrt(delta_sigma) would normalize both real quartics to v^2 = 1-u^4. The selective sign automorphism is a possible tool for proving that their two normalized generators satisfy no nonzero integer relation, because it would fix one point and negate the other. To use that argument one must still construct the exact normalized point/group maps, extend the two original embeddings into this actual tower, verify their signs, and carry nontorsion through the maps. None of those point/real comparisons is included here.

Even a verified algebraic relation-exclusion result would not by itself prove that the pair orbit is dense in the two real ovals. A genuine additive circle/uniformization comparison or a valid compact-group character argument is still required. No period independence, density, finite-component bound, m=1, or scalar-region-in-G^0 assertion is made.

## Scope and history

The historical component route was read in `quartics/quartic-318-326/docs/arithmetic.md` and the real-progression lemma of `docs/sources/quartic_v10.tex` (lines 10632–10694). It supplies prior justification for its stated compact-Lie route without assuming independent elliptic logarithms. The present alternative prerequisite does not establish that any historical argument had a new gap and does not replace an accepted theorem application.

The literal algebraic input remains D from ConcreteG8Domain. SquareReflection318 supplies the exact normal-domain and quadratic square-class theorems; its required field/characteristic-zero/nonzero-radicand inputs are checked. The constructed tower has the actual four-dimensional carrier, not a formal direct sum pretending to be a field. Its field instances follow only after the nonsquare proofs.

Only the new source packet is changed. No manuscript, accepted baseline, group law, chart signs, polynomial coefficients or source rows are changed. Source-policy and exact rational coefficient checks are not Lean elaboration or mathematical acceptance. No browser tabs were opened.
