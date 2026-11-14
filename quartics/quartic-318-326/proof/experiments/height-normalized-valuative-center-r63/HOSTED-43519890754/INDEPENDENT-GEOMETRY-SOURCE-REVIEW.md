# Independent geometry source review, run43519890754

Reviewer lean_review_resume. Canonical candidate review only against exact hosted diagnostics at head58753ec5f3b41268c5ceedae5264593b4f2aa0de; successor propagation not yet reviewed. No local Lean/Lake, user-PC access, push or proof acceptance.

## Rational infinity map
Before SHA256 f72d6593711066005480226d7c8cda9c3283acce8a3d9e9b67211fb7d4e0bace; after3e572b0d318c0e6f19261553f945fa5cf86330f32a6570f8f760c612e018a97d. Exact center-r57 log56298cf0969e68fc50d076f672403ff41c83be2e33248bd3e6f0dc156b8af259 reports recursion depth at the two final exact witness checks.

The only changes rewrite outer RingHom.comp_apply and explicitly present the target using the original infinityMap, originalFieldEmbedding and originalEmbedding on the same coordinate or generator. Checked IntegralInfinityChart318.coordinate is literally the two-stage polynomial/localization/order input in the private extensionality helper, and infinityGenerator is exactly the helper's ordered generator. The already-constructed hX and h, rational constants, localized-base extensionality and every Fin3 root are retained. No source helper signature, scalar action, sign, map, public theorem, assumption or budget changes.

This is a plausible reduction of concrete endpoint-matching work; source review cannot establish that the new rewrite/change steps avoid the same recursion bound. That remains an explicit hosted question. No source-level blocker found.

## Proper original-chart cover
Before SHA256 5db103be88c9fe3408cd5b1285eb4bda403e4c5e92d6ee27db620d147d576dc9; after07fb26ee0e81f7ec51ed26cdaff6a18fd24461b0740f8928ac884fbf37b2be2b. Exact lattice-r8 log6cc876dba3fe379310ec2c139ec76f7c6e226c0be1856d41fb450d1603c8b5f6 reports no equation theorem for originalSourceChart.

Read the exposed definition in IntegralWholeReciprocalGluing318: it is exactly Spec.map of the inverse original finite ring equivalence, composed with finiteChart. The candidate changes the goal to that literal composite and applies Scheme.Hom.opensRange_comp_of_isIso directly, rather than requesting a rewrite equation for the definition. Checked pinned MathlibOpenImmersion.lean: the lemma requires IsIso on the first morphism and IsOpenImmersion on the second, and concludes this exact range equality. Those are the same original isomorphism and finite open chart already used by originalSourceChart_open.

The arbitrary commutative ring, twist units, whole original source, restricted infinity chart, pointwise cover and overlap case split remain unchanged. There is no substitute finite ring, chart or cover assumption, and no branch/point omission. Public theorem statements/imports/options unchanged. No source-level blocker found.

Conclusion: both exact candidates are suitable for bounded hosted replay; they are not Lean-passed or independently mathematically accepted. Full closure elaboration and downstream checks remain pending.
