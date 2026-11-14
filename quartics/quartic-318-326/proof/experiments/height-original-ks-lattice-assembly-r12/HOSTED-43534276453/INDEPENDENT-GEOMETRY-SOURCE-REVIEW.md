# Independent geometry source review, run43534276453

Reviewer /root/lean_review_resume; author /root/geometry_repair_resume. Internal model source/application review only. No local Lean/Lake, kernel pass or independent mathematical acceptance. Published baseline a2d615a4183174328321ea21d60879add229de3a.

## Exact binding

- IntegralRationalInfinityMap318 before3e572b0d318c0e6f19261553f945fa5cf86330f32a6570f8f760c612e018a97d, candidate3865fb8833b519894da943be3239ce57f2326136be6728a88e3c5eb9f90fe17c. Center-r58 artifact14089193405, logb7d88b45375b9c0d90e5ae739a3d8bab1f91c89271ae7b777afb50956f1df166. Observed failure11.793s.
- LocalizedTensorRestriction318 before2e9ec64f827da222d30f7e1df494dbeab17e046a8983c5cb18dd9bdbe341a088, final candidate3854c2f1dcf457725c04d69057f455ea57edd32d49431c890ceaa5c471700332. Lattice-r9 artifact14089242976, log77b67c2b4bb9b8a9829f724fde9ca562f34471c924f3fc53b65bab6e096fa230. Observed failure1.568s.

I read both full before/after/diffs and exact logs and verified before bytes against published predecessors and both RESULT.packet_sha256 values against their respective intakes. The earlier localized draft8d3b8733 is superseded, not approved by this final report.

## Rational infinity comparison

The exact diagnostic is recursion depth at the two concrete change commands in field_restriction. The candidate moves exactly those composition/coordinate conversions to private rational_infinity_comp_ext, before substituting the large actual overlap and original Kummer field. It retains the full rational_order_ext proof rather than reducing the domain.

I read rational_polynomial_ext/localized_polynomial_ext/rational_order_ext and the original chart Order, coefficient, denominator, coordinate and infinityGenerator definitions. The source Order is still the three-root presentation over the localization of rational polynomials at the product of all three exact coefficients. The coordinate is the literal two-stage polynomial-to-localization-to-order image of X. Each infinityGenerator is exactly the corresponding ThreeRootCoordinates generator. The new helper quantifies an arbitrary intermediate commutative rational algebra A and target commutative ring T, f:A->T, the given g from the entire original order, and h from that same order. It proves f.comp(g.toRingHom)=h by agreement on the complete localized base and every j:Fin3 root. Rational constants remain controlled by ringHom ext on rationals and localization; no coefficient-domain assumption is omitted.

The concrete field_restriction uses the same originalFieldEmbedding, infinityMap and originalEmbedding. Its coordinate witness is still reciprocal_coordinate followed by original_coordinate.symm. Its root witness remains generator_original_field followed by the inverse of the exact originalEmbedding generator identity, via the same rationalOrderEquiv and openEmbedding. No sign, root order, reciprocal factor, field component or scalar action is changed. The downstream infinity_restriction still evaluates this exact ring-hom equality on every order element and uses injectivity of the original open embedding. All public theorem statements, source maps, options and budgets are unchanged.

This is source-correct staging of the normalization; whether the generic stage and concrete application remain within recursion/resource limits is still a hosted question.

## Tensor-localization scalar structure

The exact diagnostic rejects local targetAlgebra because f:B->T cannot be inferred from Algebra A T, then loses the required target algebra at subsequent declarations. The final candidate makes targetAlgebra an exposed, instance_reducible named definition with the exact old value (f.comp(algebraMap A B)).toAlgebra. It is not registered as a typeclass instance.

During review I identified a remaining avoidable inference risk in preliminary untyped installations: f alone fixes B,T but not the hidden base A. The final candidate pins all seven installations, including public result types, with `letI : Algebra A T := targetAlgebra (A := A) f`. I verified every occurrence. This chooses precisely the original given base, not an arbitrary compatible Algebra A T assumption.

The source hypotheses remain arbitrary commutative A,L,B,T, original A-algebras on L and B, the exact Away x localization L, f, and the sole invertibility hypothesis IsUnit(f(algebraMap A B x)). baseMap remains the canonical Away.lift of f.comp(algebraMap A B), with lift_eq as its scalar compatibility. rightMap remains f, whose scalar equality is reflexive for the named exact composite. The tensor lift combines those same two algebra homomorphisms through the same universal property and Commute.all for the commutative target, then forgets to the same ring hom. Its evaluations on right and left elementary tensors are unchanged.

I read the real consumer IntegralOriginalCommonRestriction318.commonRestriction/common_finite. It instantiates A=R[X], L=the Laurent localization of X, B=the full finite order, T=the old overlap, and f=the original finiteRestriction. finiteRestriction_unit supplies invertibility of that very X image through oldY; the result is composed with the unchanged finiteBaseChange inverse. Thus the new scoped algebra is exactly the consumer's prescribed scalar map and the same full common-order restriction, not a smaller open or replacement quotient.

The public baseMap/rightMap type text and targetAlgebra registration status intentionally change to state the formerly implicit original scalar action. The public lift and evaluation theorem statements and existing calling arity remain unchanged. No extra abstract algebra/tower/invertibility hypothesis is added. No imports, resource/trust options or baseline bytes change.

## Conclusion

No source-level blocker found in the two final candidates. Suitable for exact-copy propagation and hosted checking only. Final successor review must verify each source set/order, own hosted provenance and every ancillary source classification against actual predecessor bytes. Historical failed revisions and the superseded preliminary localized draft should remain distinguished from this reviewed final source.
