# Actual anchor local-square repair: nine-clause source contract

1. required_inputs

at_two retains arbitrary rational r, r≠0 and padicValRat 2 r=0. at_three retains arbitrary rational r with 0≤padicValRat 3 r, including r=0. No chosen square root or extra integrality/nonzero hypothesis is assumed. Existing denominator_unit and unit_two_num_odd produce the same reduced-denominator and numerator facts.

2. constructed_objects

The actual radicand remains 3*r^2-2. At2 the proof now binds hn8:r.num^2%8=1 and hd8:(r.den:Z)^2%8=1 using the unchanged odd_square_mod_eight, then omega combines these congruences linearly to obtain (3*r.num^2-2*(r.den:Z)^2-1)%8=0. The squared terms are atoms here, so no nonlinear arithmetic claim is entrusted to omega. This replaces only recursive Int.sub_emod/Int.mul_emod simp and its final norm_num.

3. index_and_domain_coverage

Both required exceptional primes2 and3 remain covered on their exact original domains, with every signed numerator and every positive reduced denominator. At2 the original odd-square argument covers all odd integers, not merely selected residues as new assumptions. At3 arbitrary integral ratios, including zero and nonunits, remain. The Hensel center is the actual unit reduced denominator, not the numerator or an arbitrary local point.

4. transition_maps

The existing rational_radicand_square clears precisely r.den^2, embeds the integral square through rational_square_of_integral, and divides by the actual square denominator. All Z→Z_p, Q→Q_p casts and Rat.castHom are unchanged. At3 only hp explicitly identifies the numeral norm ||(3:Z_3)|| with (3:R)^(-1), via simpa only[Nat.cast_ofNat] using PadicInt.norm_p(p:=3). No norm, normalization or comparison factor changes.

5. dependency_chase

Both own fa27/run43789364184 r31 receipts have114 full module passes ending PreparedAnchorLabels318, then this module fails: weighted2.170s, descent3.071s. Both report recursive emod simp at68 and unmatched generic natCast norm_p at92. Pinned Mathlib56a005855ea17e0b0958f73ec801ae140b0a1679 PadicIntegers norm_p has prime parameter p:N, whereas the goal norm3 uses a numeral. The explicit specialization matches the already present checked ScalarLocalSquares318 square_three_shape pattern. Same native norm_le_one, unit-denominator norm, norm2=1 and square_of_near_square Hensel producer remain.

6. public_signatures

All definitions, declaration names, hypotheses/conclusions, universes, imports, instances, expose attributes and options are unchanged. Exactly two local proof blocks change. Existing denominator, oddness, integral-to-rational transport and local-square public statements are untouched. No axioms, admissions, new public lemma, new parameter or proof expansion.

7. consumer_comparison

ActualLocalAnchorWitness318.actual_local_anchors still consumes the exact PreparedAnchorLabels actual_anchor_depths nonzero/2-unit/3-integrality data for the same ActualAnchorRatio.ratio. It applies these at_two/at_three local square theorems and physical_square using the unchanged rational physical identity to obtain both original physical-anchor equations. This is a local witness route only: no global Hasse–Minkowski, LocalGlobal, prime-value existence or Sha boundary is discharged.

8. limits_and_policy

maxHeartbeats1000000 and every other resource, root order, import, compiler timeout and trust setting are unchanged. No local Lean/Lake/compiler, user computer or upload used. Whole source inspection, receipt reconciliation and static hashes are not Lean kernel acceptance. Native source fetched from the exact official pinned commit, with retained license and provenance; no guessed modern API.

9. acceptance_boundary

Separate own receipts and predecessor intakes are bound for weighted31 and descent31. Exact source and intake bytes were compared by git show at own fa27 and integration960090b9. No old metadata or accepted snapshot is modified. Candidate32 source/current propagation require fresh independent review and hosted strict compilation/recursive audit. A previous producer pass does not prove this module or its unreached downstream roots. No full arithmetic theorem claim.

