# Simultaneous guard avoidance and component-aware progression selection

Author: `/root/advance_integer_witnesses`. This packet continues the frozen first51-row/trace packet without editing it. It is a conditional analytic/topological construction, not a claim that the actual real elliptic orbit torus has now been constructed in Lean.

## What is now proved

`AnalyticGuardAvoidance318` uses the multivariable real-analytic identity principle from Mathlib, not the one-variable isolated-zero theorem. A globally analytic real-valued function on a real normed vector space that is nonzero at zero cannot vanish on an open set. Its nonzero set is therefore dense.

Given a continuous surjective map π from that real vector space to G, with analytic pullbacks of four continuous functions g_j and nonzero g_j(π(0)), this density descends to G. No injectivity or transported topology is assumed for π. Finite intersection gives one dense open set where all four functions are nonzero. Intersecting it with an inherited open dense pole-free set still gives a dense open set, so it meets any prescribed nonempty open scalar region Ω. No independence of the two real embeddings or Haar-measure-zero theorem is required for this finite avoidance step.

A compact set K with nonempty interior is then chosen inside the simultaneous good region. Continuity supplies a positive lower bound ε_j for each |g_j| throughout K. The finite family has a common positive minimum if desired; the formal statement keeps the four individual bounds. The point is the order of quantifiers: K and all ε_j are fixed before any later progression step or translate.

`CompactGuardProgression318.positive_tail` derives arbitrarily late positive hits from compact-group recurrence. Its primary source is Mathlib's `mapClusterPt_atTop_nsmul_iff_mem_topologicalClosure_zmultiples`: every point in the closed integer cyclic subgroup is a cluster point of the nonnegative orbit at infinity. Translation by b and the neighborhood formulation of cluster points give an index n>B in every prescribed nonempty open set.

The component-aware density theorem does not assume P lies in the identity component. It starts with a dense integer orbit in the full compact group, a subgroup H, and a step k whose multiples send the full group into H. If multiplication by k is surjective on H, the actual map G→H, x↦kx is continuous and surjective; its image of the dense original orbit proves density of the kP orbit in H. `component_step_mem` derives its membership condition from component annihilation mG⊆H and m|k. A separate theorem derives nonzero integer multiplication surjectivity from a genuine surjective additive real covering map, by dividing a real preimage by k.

`compact_before_progressions` places these facts in the source's required choice order: first choose K and guard bounds, then every translated dense progression has arbitrarily late points in the interior of K. `progression_modEq` proves the literal arithmetic progression r+kn preserves each modulus dividing k.

## Actual guard consumer

`ActualGuardSelection318` imports the frozen `RealGuardTrace318`, including its explicit curve-equality transport and exact rational guard values. It uses the already proved positivity of `guardValue n 0` for every nonzero integer label to supply all four analytic-cover nontriviality inputs.

Its `select_actual_guards` conclusion constructs a single t with h=r+kt>B, the selected orbit point lying in both Ω and the inherited pole-free set, the actual elliptic point H=[h]P nonzero, and all four actual rational guard values `guardValue labels_j H` nonzero. These four nonzero values are conclusions, not premises. The actual point is nonzero by the original `RealMultiples318.multiple_P_nonzero`, with h>0 proved from k>0 and the arbitrarily large tail index.

The analytic functions are related to those exact rational guards by an explicit comparison hypothesis along the progression. This is where the future actual real orbit map must be supplied; no arbitrary abstract g_j is silently treated as a source guard.

## Exact remaining inputs

For the application to every integer input, this packet still requires construction of:

- the actual compact closure G of the pair of real P-orbits, its identity component H=G⁰, and the finite component annihilator m;
- a genuine continuous surjective additive real cover of G⁰, with analytic pullbacks of the exact guard functions;
- the comparison between those guard functions and the actual rational `guardValue` along the selected progression;
- the nonempty open scalar region Ω with the source's quantitative scalar bounds, and the inherited open dense pole-free set A;
- the actual root labels and globally compatible reciprocal charts, and the prime-pattern/local preparation hypotheses supplying the permitted CRT progression.

The positive scalar-region measure estimate in the source is still needed to prove Ω nonempty; this packet does not replace it by an assumed conclusion about the scalar coordinates. Likewise it does not replace the prime theorem with the elementary progression residue identity.

The first51-row packet converts the actual selected guard values to literal guards once its exact chart-point hypotheses are supplied. Remaining source rows, finite-place chart matching, prime-pattern and restricted-converse/pole obligations stay open. No unconditional integer-to-source theorem is claimed.

## Primary-source and historical comparison

The historical guard route is in `docs/arithmetic.md:821–1033`, with exact trace-zero functions, scalar region, compact bounds before primes, and final h,h−1 orientation. The real-progression source is `docs/sources/quartic_v10.tex:10632–10692`; the explicit component divisibility is also in Brox v3 `docs/sources/diophantine_optimization_20261106_v3.tex:3249–3302`. Only its component argument is used, not the old h−4 residues. `PrimeCRTAssembly.lean` supplies the existing arithmetic congruence and component-compatibility facts.

The historical disposition is prior justification found; this packet formalizes parts of that route. It does not identify a newly discovered mathematical gap. The current formal disposition is partial: zero avoidance, uniform compact bounds, recurrence, component-aware step density, and their actual-guard consumer are established under the displayed geometric/arithmetic inputs.
