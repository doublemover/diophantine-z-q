# Working arithmetic-to-real-group bridge

This is changing, unaudited work. It is not an accepted packet and must not enter a source manifest yet.

CoherentAdditionU318 has passed strict compilation (the final cosmetic warning cleanup also passed). It proves the exact coherent u-coordinate addition law for all actual elliptic half-points. A reciprocal-source-point computation gives the tangent case. Equal abscissae split into equality or negation, and the previous oriented secant identity supplies the remaining case. This is equality of u, not merely of u squared.

CoherentAdditionV318 is drafted and the corrected strict check is queued. It uses the actual non-torsion integer orbit to establish the same-square branch condition required by ReciprocalGroup318.actual_add. Exact source-point comparison plus the proved u law then identifies the oriented v-coordinate; the inverse case is checked directly. The first attempted check exposed elaboration issues in the field/commutative-ring instances and one uncleared inverse denominator. Those are being repaired without changing any frozen predecessor.

RealCoherentOrbit318, ActualCyclicClosure318 and ActualCyclicGuards318 are drafted, not yet compiled. They are intended to identify the exact coherent coordinates in both real embeddings with integer multiples under the new rational full-oval group law, construct their actual compact closed cyclic subgroup with dense positive tails, and compare the same four literal guards on that group. No check of these drafts is claimed.

The dependency forward-real-oval-group-r1 is undergoing its final six-source strict replay. All four associativity/analytic sources and the group wrapper passed earlier; the final compactness wrapper had a subtype-membership elaboration error that is corrected and awaiting recheck. The final clean replay currently has its first three modules complete and is queued for the rest.

The shared serial compiler queue stopped granting acquisitions after about 2026-11-09 04:55 UTC and the owner file is absent. Other workers report the same state. No parallel compiler or lock bypass has been attempted. Parent and integration worker are aware.

The actual closed cyclic subgroup is not assumed equal to the whole two-oval product. An analytic additive cover of its identity component, the finite component quotient and scalar-region nonemptiness remain open. Existing Mathlib AddCircle density results require an actual additive circle comparison, which has not yet been constructed. A trigonometric analytic surjection onto the oval is not such a homomorphism. The historical real-progression lemma at quartic_v10.tex lines10631-10694 gives prior justification for the compact-Lie-group route, not a ready formal theorem.

A possible explicit next prerequisite is time reparameterization of the current angle curve: t(theta)=c integral_0^theta (1+sin(s)^2)^(-1/2) ds, where c=D^(-1/4). It has positive bounded-below derivative. Its analytic inverse should produce the additive one-parameter curve by uniqueness for the polynomial vector field (u',v')=(v,-2D u^3). This is a plan only, not a proved theorem or permission to assume an independent-period condition.
