# Literal rational numeral self witnesses: nine-clause source contract

1. required_inputs

The full original physical_identity and local_depths telescopes are unchanged: arbitrary signed labels Fin4→Z, each Odd, labels1≠1, arbitrary natural N, and the same N≤2+2*padicValInt3(labels1-1). Existing native prime facts, actual_product_depths, inverseNorm nonzero, unit_add_small and minimum valuation are unchanged. The only new proof-local inputs are rational-numeral specializations of the existing padicValRat.self theorem.

2. constructed_objects

ratio remains4096*normProduct labels+inverseNorm(labels1)/3^N in Q. Introduce hself2:padicValRat2(2:Q)=1 and hself3:padicValRat3(3:Q)=1 by simpa using native self with the same explicit natural prime parameters and same norm_num proofs of1<p. Rewrite with those typed witnesses. No mathematical definition, object or additional premise is created.

3. index_and_domain_coverage

Every Fin4 label, negative odd labels, N=0 and all N satisfying the original bound remain included. labels1≠1 and all original nonzero conditions remain exactly. The two exceptional primes2 and3 retain their original literal values. No finite case checking or generic-only substitute replaces the quantified statement.

4. transition_maps

The Nat→Q cast in native self is normalized into the literal rational numeral only at the local witness boundary. No ring homomorphism, coefficient action or normalization map changes. The literal physical anchor identity and scale3^N, inverseNorm, normProduct and rational division are untouched.

5. dependency_chase

Own exact run43737192432 at8d18 has112 complete passes in each29 lane then two errors at38/61. Rewrite sees native pattern padicValRat2 ↑2 versus target padicValRat2 2 and similarly3. Earlier proof errors are absent but the full module still fails. The retained official pinned Mathlib Basic source states self with implicit natural p, hypothesis1<p and cast rational argument. Two typed simpa witnesses reconcile exactly that cast syntax, then the unchanged pow/mul/div and additive valuation chase consumes them.

6. public_signatures

All public names, full hypotheses and conclusions, definitions, universes, declaration order, imports, attributes and options remain byte-identical. Only two local have declarations and replacement of two rewrite-list entries are added. No new axiom, admission, expose attribute or implicit public parameter.

7. consumer_comparison

The first witness feeds h212 via4096=2^12; the same product depth p2 then gives hfirst2. The second witness feeds hsecond3 via the existing hdeep inequality. Both original unit_add_small and min_le_padicValRat_add constructions and final tuple hr,hv2,hsum remain untouched. Downstream consumers receive exactly the original ratio theorem.

8. limits_and_policy

Existing maxHeartbeats1000000, imports, root order, ordinary wall timeout, runner and policy are unchanged. No local Lean/Lake/compiler invocation. Source inspection and Python binding checks are not a compiled proof. No new diagnostics, workflow phase or resource limit changes.

9. acceptance_boundary

This envelope is a candidate only, bound separately to both own29 receipts and reconciled unchanged source bytes from8d18 to current60747. It does not claim ActualAnchorRatio passed. Immutable30 successors require independent canonical source and current propagation review, durable backup and hosted replay. No baseline promotion or acceptance of unreached descendants.

