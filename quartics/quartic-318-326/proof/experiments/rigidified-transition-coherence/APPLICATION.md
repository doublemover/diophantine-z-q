# Application contract: actual rigidified pullback and coherence

Status: draft, not independently accepted, not Lean-compiled locally. This
contract describes this packet only. It changes neither the manuscript nor
any historical verdict or accepted-baseline source. Source versions and exact
bytes are bound by `intake.json`, `SOURCE_SHA256SUMS` and `DEPENDENCIES.json`.

1. **Required input.** `CompatibleIso` in the unchanged
   `RigidifiedLineIsomorphism318.lean` stores an isomorphism of the original
   `Scheme.Modules` objects and equality against both specified
   trivializations. The new operations use this exact structure, not a
   replacement class relation. Identity/inverse/composition require no
   global-function assumptions.
2. **Constructed input.** `RigidifiedPointedPullback318.restrictionComparison`
   uses the actual `Scheme.Modules.pullbackComp` maps on an arbitrary square
   `e' ≫ a = b ≫ e`. Its `line` uses the original line pullback, transports
   the given trivialization, then uses the original structure-module
   `IdentityCotangent318.pullbackUnitIso`. It does not choose an unrelated
   trivialization from class equality.
3. **Domain and indices.** The pointed-square construction covers all schemes
   in the declared universe and all original rigidified lines. No affine,
   reduced, flat or field restriction is added. The contact comparison family
   permits every index type, but all its entries lie on the same field family.
   It is explicitly not a construction of a covering family or its overlaps.
4. **Transition directions.** A compatible isomorphism `L → M` followed by
   one `M → N` is composed in that order. Pointed pullback sends the actual
   sheaf isomorphism along `a`; its compatibility proof uses naturality of
   the original composition comparisons. `mapIso_identity` and
   `mapIso_compose` are equations of compatible isomorphisms. Pullback
   directions match the existing relative quotient map, as certified by
   `relativeClass_line`.
5. **Hypothesis discharge.** Selecting a transition from equal relative
   classes requires an actual section identity and bijective actual `appTop`
   evaluation. Existence comes from the unchanged original-relative-class
   comparison; uniqueness uses its injective component. In the contact
   consumer these are `ContactFieldRigidifiedClass318.section_eq` and
   `section_appTop_bijective`, on its unchanged `K`, `X`, `p`, and `e`.
   The all-test consumer instead uses the exact `q`, `e`, `testSection` and
   `test_evaluation_bijective` of `ContactUniversalRigidifiedClass318`, with
   the fixed actual source coefficients `SourceTwistArithmetic318.units`.
   This supplies rigidity for every scheme test over that exact field base.
   The generic `UniversalSectionEvaluation318` theorem requires flatness;
   this specialization discharges it because the test maps to a field.
   No claim is made for unrelated arbitrary nonfield base schemes.
6. **Resulting object identity.** `RigidifiedClassQuotient318.toRelative` is
   literally the original `classMap p` applied to the underlying original
   line class. Surjectivity uses actual section-rigidified representatives;
   injectivity uses actual compatible isomorphisms. `equivalence` is this
   bijection, not a newly stipulated group or Picard scheme. Chosen transition
   morphisms remain original module-sheaf maps, and
   `transition_hom_cocycle` exposes the exact equation a later gluing
   construction would consume.
7. **Coefficients and exceptional cases.** Generic modules use the original
   scheme/module-sheaf universe and coefficients. The contact specialization
   keeps the actual finite field extension, original parameters `c : Fin 4 → ℚˣ`
   and `t : ℚ`, and the already constructed section. No rational point on the
   original rational family or degree-zero hypothesis is inserted. There is
   no claim about degree, norms, Euler factors, or a polarization here.
8. **Downstream boundary.** These results supply actual pullback and coherent
   comparison operations for a future descent construction. They do not
   prove effectiveness of descent or replace the original associated fppf
   sheaf with the naive quotient. No accepted final theorem, height input,
   source-arithmetic premise, manuscript passage or historical disposition
   is changed by this packet. `ContactTestRigidifiedCoherence318` extends
   the construction to every original scheme test, and its
   `transition_pullback` identifies the chosen transition with the literal
   pulled-back sheaf isomorphism. No cover diagram or effective descended
   object is supplied by that compatibility theorem.
9. **Evidence and acceptance.** Exact producer locations and hashes are in
   `DEPENDENCIES.json`; exact new declarations are in the five modules named
   in `intake.json.new_modules`. Source-only validation has passed. No
   new-source compiler result, recursive axiom-audit result, or independent
   acceptance is claimed. Hosted checks and bounded independent review must
   precede any admission to the accepted snapshot. A structural PASS is not
   mathematical acceptance.
