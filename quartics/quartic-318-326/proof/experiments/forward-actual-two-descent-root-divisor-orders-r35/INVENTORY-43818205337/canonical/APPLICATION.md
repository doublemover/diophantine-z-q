# Source150: preserve guard scalar expression before zero rewrite

1. required_inputs

The entire select_prefix statement is unchanged: arbitrary rational S,q,t with t and its contact nonzero; all four integer labels nonzero; all seven natural CRT parameters with the exact positivity, coprimality, gcd16 and64-divisibility conditions. The same bound B and all original hypotheses remain. No nonzero guard or solution is newly assumed.

2. constructed_objects

The sole proof delta replaces simp[he] at ht with rw[he] at ht followed by norm_num at ht. ht is the exact guard lower bound already produced by UnconditionalRealCRTPrefix. The explicit rewrite uses the assumed zero of the same rational guard before broad simplification can change integer scalar action notation to natural scalar action. The resulting zero cast and absolute value normalize to0; unchanged linarith contradicts the strictly positive margin.

3. index_and_domain_coverage

The same chosen h from the original B+1 CRT selection is reused for every congruence, point-nonzero result, scalar bound, all four guards, input coordinate and root equality. The proof still handles arbitrary j:Fin4 and all admissible labels. No sample, fixed contact parameter or alternate index is introduced.

4. transition_maps

The rational guard is still evaluated at ((h:ℤ)•P) and cast toℝ inside absolute value. The repair rewrites that rational guard equality in its existing typed occurrence, without changing the scalar-action map, cast, point or bound. Native Lean rewriteLocalDecl applies the supplied equality to the local hypothesis; no new rewrite axiom or change in group action is used.

5. dependency_chase

GeneratorScalarProgression.margin_positive proves0<margin from the actual nonzero labels. UnconditionalRealCRTPrefix supplies margin<abs(guard) at the same integer multiple. Explicitly rewriting guard=0 gives margin<0, contradicting positivity. The same guard proof already appears verbatim in Source107CRTWitness, which independently passes in each own inventory. That supports this repair but does not certify Source150 candidate elaboration.

6. public_signatures

All imports, namespace, theorem telescope and conclusion, witness construction, first150 row count and all other proof lines are unchanged. One simplifier invocation becomes an explicit rewrite plus numerical normalization. No new theorem, hypothesis, enumeration, admission, axiom, resource option, diagnostic or compiler/trust change.

7. consumer_comparison

The unchanged ContactChainWitness.witness_first150 receives hzero,hone,the original free t/nonzero-contact hypotheses and the guard nonvanishing just proved. Its complete original fill chain covers exactly the first150 of288 rows, preserving the input and all four root equalities; remaining138 rows and pole realization are not claimed. No downstream theorem using this result was invented; the actual local producer/application chain is included in full.

8. limits_and_policy

Evidence is an independently authenticated dependency-ready INVENTORY, not a normal first-failure replay. Each own weighted34/descent34 inventory at marker e51/requested source15d has117 compile_pass,2 compiler_error, and1185/1180 blocked_by_import. Source150 fails1.417s/1.418s separately. The117-successful-module audit covers4188 declarations only; packet acceptance remains false. Own production43817651313 still stops at PreparedAnchorSource; its unknown-fvar issue remains unresolved and unchanged here.

9. acceptance_boundary

Both own inventory JSON/log/intake/source identities and successful-subset audits are bound separately, with published15d/e51 source reconciliation and own production failure retained. This observed independent error is not classified as an unreached preventive edit. Canonical and current propagation reviews are required before any isolated successors. No local Lean, upload, user computer, main edit, whole packet acceptance, baseline promotion or full arithmetic theorem claim.

