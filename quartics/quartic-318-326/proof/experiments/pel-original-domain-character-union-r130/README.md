# Cotangent frame simplification repair

This is a narrow successor to frozen `pel-original-domain-character-union-r113`. Only PolynomialRelativeCotangentFrame318.lean changes: RingHom.id_apply is added to the simp-only list at line53, resolving the identity-ring-hom wrapper exposed by hosted batch214. All other 998 Lean sources are byte-identical predecessor copies, pinned in COPY_BINDINGS.json. Statements, hypotheses, maps, scalar structures, ideals and consumers do not change. Prior review is historical; independent review and hosted checking of this successor remain pending. No local Lean build or profiling was run.

The exact diagnostic is build/ci214-cotangent/logs/PolynomialRelativeCotangentFrame318.log. This propagation prevents the same known failing source from being rescheduled in another active closure. Frozen predecessor files are untouched. The mathematical scope and limitations in the historical description below remain unchanged.

## Historical predecessor description

# Original primitive analytic root charts

Every element of the actual localized polynomial coefficient ring is now proved analytic on its own principal open. Every simple root of the same produced original primitive equation has a complex analytic local graph and an open chart on the independently induced whole ambient root locus, in the same two projected coordinates. This applies to every root, not only points known to lie in the theta image. Candidate-order identification, original-sheet exhaustion, analytic-image equality, rational descent and represented Jacobian identification remain separate.

This is a new reconstruction from retained mathematical sources, not acceptance based on a lost-work report. The source is submitted for independent review and hosted compilation. The inherited union and its contracts remain retained historical evidence. This successor changes only five added modules and one explicit Complex.Basic import; all predecessor mathematical declarations remain unchanged.
