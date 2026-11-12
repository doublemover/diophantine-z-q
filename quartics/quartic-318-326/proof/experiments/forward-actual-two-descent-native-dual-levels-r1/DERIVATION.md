# Original-level native dual construction

## Inputs and exact carriers

Fix n in Q, n nonzero. Let S be the independently constructed `actualPrimarySelmer n hn`, with its genuine all-place condition, and give the distinct synonym `DiscreteSelmer` the discrete topology. The source of the final homeomorphism is exactly `PontryaginDual (DiscreteSelmer n hn)`: continuous complex-Circle characters with Mathlib's compact-open topology. Neither a rational-circle character group nor a renamed free rank-one module is substituted for it.

For each k >= 0, S[k] is the actual additive kernel of multiplication by 2^k in S. `DiscreteSelmerLevel` is its multiplicative synonym, with discrete topology. In particular k=0 is the trivial subgroup. The inclusion and every transition i <= j are literal subtype inclusions; the latter use the proved exponent-monotonicity lemma. Applying native `PontryaginDual.map` constructs continuous restriction homomorphisms. There is no omitted level, selected cofinal set, or changed inclusion direction: the characters run contravariantly from level j to level i.

## Reconstruction and identity

For a compatible family F, evaluate x at `primaryExponent x`, whose annihilation was already proved. To compare this with any other annihilating level k, use max(primaryExponent x,k). Compatibility with both original inclusions identifies the two values. For additivity, use a common maximum annihilating x and y, hence x+y, and the actual character law at that level. Zero is handled explicitly at level 0. Discreteness of S supplies continuity of the resulting character, not a hypothesis about F.

Restriction of the reconstructed character is literally F at each level. Conversely all restrictions detect a character, since each original element has a proved annihilating level. This proves the entire compatible-family universal property, not only uniqueness or a map into an unspecified limit.

The compatible-family carrier is a subgroup of the product of the actual native level duals, using their original group laws and inherited product topology. The restriction map is continuous coordinatewise. It is a group equivalence by the reconstruction and separation proofs. The original native dual is compact because its source is discrete (Mathlib PontryaginDual native instance). The literal product and its subgroup are Hausdorff because the original native duals are Hausdorff. A continuous map from compact to Hausdorff is closed; `Equiv.toHomeomorphOfContinuousClosed` therefore supplies inverse continuity. The final coordinate theorem is definitional equality with the original restriction, preventing an unrelated choice of homeomorphism.

## Scalars and finite levels

The scalar on S is the existing independently defined `actualSelmerPadicEnd`, given on an element killed by 2^k by the value of `PadicInt.toZModPow k a` times that element. Its discrete continuous homomorphism has native Pontryagin pullback exactly equal to the pre-existing `nativeDualScalar`. This gives continuity in the character argument for each fixed a, not joint continuity.

Applying a character to the scalar formula gives exactly the residue-power formula. Equal residues act identically on restrictions; zero residue annihilates the level. Original level annihilators are kernels of continuous restriction, hence closed, and are stable under every actual scalar. They decrease with k and their intersection contains only the identity character.

Only the final finite-level result uses `Finite (DoubleQuotient n)`, its cardinal bound <=8, actual all-place cardinal 8, and `ActualReducedDuality n hn`. The existing theorem gives an actual group equivalence S ≃ Pruefer. Restriction of that equivalence and its inverse to the actual kernels gives an additive equivalence at every k, preserving the same exponent. The existing Pruefer level coordinate supplies cyclicity and cardinal 2^k. Finite discrete level groups are compact, so the native finite-domain Pontryagin instance supplies finiteness of their duals. These hypotheses are not silently used in the preceding inverse-limit construction.

## Exact source/API comparison

- Predecessor `ActualTwoDescentPrimaryPadicScalar318`: the scalar-at-level theorem explicitly accepts any annihilating k; no global bounded exponent is assumed.
- Predecessor `ActualTwoDescentHigherCohomologyDirectedMaps318`: exponent monotonicity supplies actual transition membership.
- Predecessor `ActualTwoDescentPrueferLevelCoordinates318`: original additive killed subgroup, exact cardinal, and actual cyclic coordinate.
- Pinned `PONTRYAGIN-PRIMARY/Mathlib__Topology__Algebra__PontryaginDual.lean`: definition as continuous complex-Circle homomorphisms, native compactness for discrete source, Hausdorffness, and continuous contravariant `map`.
- Pinned `LATTICE-PRIMARY/Mathlib-Topology-Homeomorph-Defs.lean`, `Equiv.toHomeomorphOfContinuousClosed`: requires exactly a bijection, continuity and closedness. Source compactness and target Hausdorffness discharge closedness on the original topologies, not a transported one.

The only predecessor source edit responds to hosted-a1735 `UniformScaledPoleDomain318:76`: its pair projections survived rewriting and blocked `exact_mod_cast`. `simp only [Prod.fst, Prod.snd] at hb` removes those projections before that same cast proof. This does not alter any threshold, quantifier, coefficient or conclusion. The failed predecessor remains unchanged in its own packet.

## Limits of the evidence

The new Python regression checks exact finite dyadic restriction, all transition pairs, reconstruction, scalar residues and annihilators through exponent 8. It does not check Lean, topology, or arithmetic duality. No local Lean execution or profiling has been used. The 1,178-source closure and its source policy have structural checks only pending hosted Lean. Source review is distinct from kernel validation and final mathematical acceptance. The global pairing, restricted analytic converse, analytic-to-rational theorem, same-index rational twist points, and full integer-characterization remain open.
