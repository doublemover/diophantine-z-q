# Observed normalized sign-action repair contract

Run 43597228569, published head 2af419e128047c483b3cdc0ba5e4d65c09d7c4ce. Exact before/after/evidence hashes are bound in SIGN-MANIFEST.json. Isolated source candidate only, with no local Lean or kernel acceptance.

## 1. Required source input

The native chart definitions require a pair (u,s) with s 0 = 1 and all four square equations, and an InfinitySigns vector with its zero coordinate normalized to one. FourBinaryCharacters318.coordinate_square gives each actual coordinate character squared equal to one for every group element. The proof already supplies those inputs. The two new `change` commands expose precisely the existing pair/function projections before the same property rewrite; they add no assumption or auxiliary model.

## 2. Constructed objects

Retain FinitePoints b, InfinityPoints b, all eight InfinitySigns, Completed b and the coinduced FourRootGluedTopology topology. The finite map fixes t and sends z_i to epsilon_i*z_i. Infinity sends u to epsilon_0*u and s_i to epsilon_i*epsilon_0*s_i. Every data field, map and public statement remains unchanged. Only proof expressions for the two normalization obligations and the finite involution product-extensionality application change.

## 3. Index and domain coverage

Every b:Fin 4→ℂ, g in the entire four-bit character group and every finite or infinity chart point remain quantified. All four character coordinates, including i=0, and both summands of Completed are retained. There is no distinctness, nonbranch, bounded, finite-sample or nonzero-coordinate assumption added to the action or involution.

## 4. Transition maps

The original infinity_chart equality still compares the actual action composed with infinityChart to infinityChart composed with the exact transformed pair. Both zero and nonzero u branches, the native toFinite overlap and its base b0+u^-2 are unchanged. The nonzero branch retains epsilon0≠0 and u≠0, so the same cancellations are available. Continuity still uses BOTH independent glued chart maps, not transport from original PEL points.

## 5. Scalars and normalization

The normalized ratios use epsilon_i/epsilon_0 = epsilon_i*epsilon_0 because epsilon_0²=1. The changed normalization targets are literally epsilon_0*epsilon_0*s0=1, followed by the existing s0=1, multiplication and square rewrites. No sign or scalar is dropped. Finite involution uses the same coordinate_square identity; product equality is now split into its unchanged base-coordinate reflexivity and the same pointwise root calculation.

## 6. Actual consumers and object identity

PELOriginalCompletedContactDeck318.equivariant consumes this exact action and continuous theorem to extend the original roots_action from the actual dense RegularSource to ALL original points. actual_comparison_equivariant consumes this exact homeomorph, not an arbitrary point permutation. FourRootCoordinateRingSigns318.finite_point/infinity_point identify evaluation of the native quotient-ring sign endomorphisms with these precise chart maps. FourRootSchemePointEquivariance318.completed_equivariant and original_equivariant use the same maps for actual SchemePoints, while FourRootActualResidueInertia318.infinity_sign_fixed/infinity_inertia consume the same normalized infinity action. Exact consumer sources are retained in primary evidence.

## 7. Exceptional cases

The eight infinity points are not collapsed, and finite branch roots may vanish. sign_ne is proved for every character, not assumed. The proof still handles u=0 separately from u≠0 and every finite and infinity point in the involution. The candidate does not claim all downstream log errors are necessarily secondary; hosted replay must determine any remaining elaboration/kernel defects.

## 8. History and observed evidence

Both authentic zero-r43 and cotangent-r49 artifacts report the same two rewrite failures on unreduced pair/function projection targets and the failed `apply Prod.ext rfl` in finite involution. Subsequent errors include missing infinity declaration and a signs kernel conversion mismatch. The candidate corrects the three earliest independent proof presentations; it does not assert those later diagnostics have passed. Both preceding FourRootCompletedHausdorff318 full modules passed in this run. Own artifact ZIP digests, RESULTs, full logs and exact published intakes are bound, and published before source identity is verified.

## 9. Verification boundary

Public telescopes, data construction, imports, production options and resources remain unchanged. No sorry, axiom, placeholder, new assumption, component selection or caller premise is introduced. This is a source-supported candidate, not a Lean/kernel/full-packet result. Fresh independent source review and packet-specific nine-obligation propagation review precede any integration. The mathematical target and exact consumer objects are not weakened.
