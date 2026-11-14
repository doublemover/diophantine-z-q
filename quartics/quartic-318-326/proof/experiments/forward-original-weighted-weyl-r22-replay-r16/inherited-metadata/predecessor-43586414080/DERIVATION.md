# TwoTwistPointRealization318: expose the original rational point-pair construction

## Exact observed scope

Proof-only run43582938856 at6fe85071934d36d22cfdbd7c503f6b9a54e6ef18 verifies PreparedIntegerSource318 in both forward packets (2.722/2.671s). Own descent-r12 artifact14109633205 and weighted-r12 artifact14109801146 first fail TwoTwistPointRealization318 (2.822/2.672s). Their exact logs agree after packet-name-only normalization. The only hard error is exported pointPair_parameter rfl: Realization.pointPair is not exposed. Earlier unused-tactic warnings are retained and not counted as additional failures.

The sole edit is @[expose] on Realization.pointPair. Its structure value, all field proofs, every theorem statement and all other definitions remain byte-identical. This exposes an existing definition for exported reduction; it adds no axiom, arbitrary point or existence assertion. The later diagnostic-only tip has identical packet sources, but no diagnostic-run result is used as proof-run evidence.

## Required inputs and actual constructed objects

Realization b retains beta,theta,c,d,n, nonzero c/d, both original rational squareclass identities17b=beta*c² and (17b)²(1-b/17)=theta*d², and actual SquareclassPoints on the two original curves with the shared n. Each point has a nonzero root and its literal ordinate equation. The output remains PointPair b, at the SAME original pole b, with parameter n*(c/first.root)²; s=second.root*d/first.root; y1=first.ordinate*(c/first.root)³; y2=second.ordinate*(c*d/first.root)³. No CM model, twist, curve parameter, point or squareclass is substituted.

## Complete quantifiers, maps and coefficients

Every b and every Realization b satisfying the original fields remain quantified. The first and second class equalities and both point equations remain the only arithmetic conversion inputs. The original root/d nonzero proofs establish s≠0; denominator clearing and ring proofs are unchanged. All rational coefficients, powers2/3, factors17 and3, signs, and the second curve parameter n*theta are retained. The formula for pointPair_second_scale continues to carry the actual second squareclass factor, not a free twist. The equal-twist case theta=1 and zero ordinates are not excluded, and no new n≠0 or b≠0 premise is imposed on pointPair.

## Actual consumers

Same-module pointPair_parameter is the direct exported projection consumer and pointPair_second_scale uses it with the original second_class. Realization.certificate applies the original PointPair.certificate to this exact point pair when its existing b≠0 argument is supplied. External PreparedTwistSource318.current_source_from_twists calls the actual hfinish with R0.pointPair, R1.pointPair, R2.pointPair, R3.pointPair and the SAME Anchor at line78. It retains the original common selected h, all four actual poles and every local-unit/realization input. It does not infer rational-point or Anchor existence from bounds. Those actual producer/consumer sources are retained.

## Verification boundary

Before81e026c9d599da4665c0adc97d3a8feb9959ead905d0bfc765f7abfe63d5e166; candidate4c529c579596ed635a8750aa70d6a73e6a0161e158f66abe1674d4210b37d4df. Each original1299/1304 ordered closure changes only this canonical root and retains its own RESULT/intake/digest evidence. All imports/options remain unchanged and no speculative ScalarPolePreparation fix is included. Distinct review and hosted Lean remain required; no local compiler, candidate kernel/recursive audit or full arithmetic acceptance is claimed.
