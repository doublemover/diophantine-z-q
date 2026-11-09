# Full original orbit density and the mixed-CRT prefix

This successor preserves all 43 sources of the invariant-clock packet except three narrow inherited API repairs. It adds three modules connecting the exact arithmetic generators, actual real topology, and original source-prefix witness in one chain. The source proof is implemented; hosted Lean elaboration and recursive axiom checking are pending. No local Lean compilation was run.

## Actual objects and topology

The input is not a newly chosen torus generator. It is `ActualCyclicClosure318.generator = pairOrbit 1`, where each coordinate is the real coherent chart of the literal arithmetic elliptic point `LocalGenerator318.P`. The embeddings are exactly the positive and negative embeddings of Q(sqrt(2)). The existing field-normalization chain supplies `NormalizedOvalIndependence318.oval_integer_relation` for the two exact normalized full-oval generators. Their group law is the existing rational quartic operation, with its existing real subtype topology.

The full oval is important: the reciprocal Weierstrass map is not claimed injective or homeomorphic. It identifies simultaneous sign changes and takes both u=0 points to elliptic zero. Instead, the retained invariant-clock construction gives an additive homeomorphism between the actual full normalized oval and one additive circle with a single common positive period. The new code rescales that circle to the unit circle, using both the actual additive equivalence and corresponding homeomorphism.

## The finite-product character criterion

`TorusCharacterDensity318.denseRange_zsmul` assumes exactly that every nonzero integer character has value different from 1 on the chosen generator. It constructs H as the topological closure of that generator's integer multiples. H is an actual closed subgroup of the original finite product of unit circles, hence compact and Hausdorff. Normalized Haar measures on H and the full torus have total mass one; they are invariant and positive on nonempty open sets.

Averaging after the inclusion H -> G and averaging on G are continuous complex-linear functionals on continuous functions, with norm at most one. For each nonzero Fourier character, translation by the actual generator multiplies the integral by a scalar different from 1, while Haar invariance leaves the integral unchanged. Therefore both integrals vanish. For the zero character, both integrals equal one.

The pinned `UnitAddTorus.span_mFourier_closure_eq_top` theorem gives uniform density of the complex linear span of those characters. The closed equalizer of the two continuous linear functionals contains that span and therefore all continuous functions. Apply this to the complexification of the distance to H. Its integral on H is zero, so its real integral on G is zero. Nonnegativity gives almost-everywhere zero; continuity and positivity of Haar measure on nonempty opens give everywhere zero. Since H is nonempty and closed, every point lies in H. This is the missing full-product density argument, not an inference from arbitrary compact-group independence.

Pinned APIs were inspected at mathlib revision `56a005855ea17e0b0958f73ec801ae140b0a1679`: `Analysis/Fourier/AddCircleMulti.lean`, `MeasureTheory/Measure/Haar/Basic.lean`, `MeasureTheory/Group/Integral.lean`, `MeasureTheory/Measure/OpenPos.lean`, `MeasureTheory/Integral/Bochner/Basic.lean`, `MeasureTheory/Integral/Bochner/ContinuousLinearMap.lean`, `MeasureTheory/Function/LocallyIntegrable.lean`, and `Topology/MetricSpace/HausdorffDistance.lean`.

## The actual no-character hypothesis

`ActualPairDensity318` constructs the coordinatewise additive equivalence and homeomorphism from the original pair to two unit circles. Evaluating a two-dimensional character at the image of the original generator equals applying `AddCircle.toCircle` to n0 times its first coordinate plus n1 times its second coordinate. If this character value were 1, injectivity of `toCircle` would give an actual additive-circle relation. Applying the same additive circle-to-oval equivalence to both coordinates would give the exact normalized oval relation. `oval_integer_relation` then forces n0=n1=0, contradicting the frequency's nonzero hypothesis.

The finite-product criterion therefore applies with no caller-supplied density or no-character assumption. Transport through the inverse homeomorphism, together with the existing `pairOrbit_zsmul` identity, concludes `DenseRange pairOrbit` for the literal original coherent orbit.

## Same-index arithmetic consumer

`UnconditionalRealCRTPrefix318.select_prefix` supplies `ActualPairDensity318.pairOrbit_dense` to the existing exact mixed-CRT prefix theorem. Its conclusion uses one and the same positive integer h for all of:

- h greater than the requested bound B;
- h congruent to 0 modulo Pi^e Mminus, to 1 modulo Mplus, and to h0 modulo L;
- the literal nonzero point h P;
- the original scalar bound 1/(100 sqrt(7));
- all four fixed strictly positive guard margins;
- the original rational input q in witness slot zero;
- all first 51 literal source rows at the chosen S;
- the existing fixed signed root convention for the same h and h-1 charts.

The full pair is connected, so the actual cyclic closure is connected. The exact return modulus is m=1. The original generator is in the required scalar/guard region, with fixed margins chosen before the prime moduli. Thus this final theorem has no real-density, component-return, or scalar/guard intersection premise.

The arithmetic moduli premises are unchanged: positivity, four stated coprimality conditions, gcd(Mminus,L)=16, and 64 dividing L and h0. Producing these prime-pattern data remains separate. The remaining 237 of 288 source rows and final source `HasSolution` consumption remain separate. This packet does not prove the full arithmetic theorem.

## Hosted failure preservation and narrow repairs

Run 42579994089 on cee0c58 passed 25 predecessors, including the prior ActualCyclicClosure repair, and then failed ActualCyclicGuards. Its exact RESULT and log are preserved under `forward-oval-invariant-clock-r1/hosted-failure-42579994089`; the tested source bytes are unchanged. This successor adds `sub_eq_add_neg` to the exact shifted-orbit proof and uses the pinned global `natCast_zsmul` instead of nonexistent `Int.natCast_zsmul` in ActualCyclicGuards, ActualCyclicProgressions, and ActualMixedCRTPrefix. No arithmetic point, sign, guard, index, or hypothesis changes.

## History and acceptance

The earlier manuscript already gave a compact-Lie/component and analytic-guard route; its actual argument was checked in arithmetic.md lines 821-1033 and quartic_v10.tex lines 10632-10694. This stronger full-density route is a newly formalized alternative and is not presented as repairing an unproved historical assertion. Its revised application requires fresh review. Static source-policy, dependency-closure, and Python test success do not establish Lean elaboration or mathematical acceptance. No `sorry`, `admit`, new axiom, or conclusion-as-premise is introduced.
