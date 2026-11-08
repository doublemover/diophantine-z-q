# Retrospective audit of our existing maps

This review answers the specific concern about isomorphism claims already made in the 318/326 contribution. It examines actual maps and their inverse equations or universal properties, not just upstream literature. Target source snapshot: dea5d91b63e43d5f3ba9874c64463a0f28ff934b. Exact public-file hashes and authorship limits are in intake.json and the individual decisions.

## Findings

- [Charts, base change, negation and product transports](charts-base-change/REVIEW.md): 19 source modules. The overlap and coefficient changes have explicit two-sided algebra inverses, negation squares to the identity on the actual glued scheme, and the intersection/product comparisons use genuine categorical pullbacks. Local addition is not called an isomorphism or a completed global group law. The reviewer's own generic cover helper is excluded from independent acceptance.
- [Contact fields and normalization charts](contact-normalization/REVIEW.md): 55 Lean modules plus scoped prose and interfaces. Actual field, coordinate-ring and affine-Scheme inverse/composition witnesses and the same-field normalization joins were inspected. One prose correction is required, described below. Projective/Jacobian/PEL identifications and the unfinished full chart intersection remain separate.
- [Hodge, differential and tensor maps](hodge-tensor/REVIEW.md): 17 claim families across 38 sources. Constructed inverses, canonical maps and full-subopen sheaf criteria were traced. A split injection is not presented as an isomorphism; Hodge evaluation retains its domain hypothesis; contact tensor frames and sections remain local.
- [Torsion, splitting and the categorical equalizer](torsion-equalizer/REVIEW.md): 38 packet sources. Actual CRT/interpolation maps and both directions were checked, as were arbitrary-ring hypotheses and the arbitrary-Scheme equalizer property. No global multiplication kernel, full additive marking or PEL identification follows from these statements.
- [Our classical CM/PEL/metric producer arguments](classical-producers/REPORT.md): the actual maps in three notes and their formal consumers were inspected, with predecessor authorship disclosed. The CM note uses isogeny, the map E/E[2] to E is induced through [2] rather than calling [2] invertible, and the KS argument uses the actual forget-level universal fiber. Formal realization hypotheses remain explicit.

- [Analytic and modular comparisons](analytic-modular/REPORT.md): 29 Lean sources and eight packet READMEs. The actual complex algebra/Spec fiber isomorphism, elliptic torus additive equivalence and Gamma_H quotient homeomorphism were inspected separately from the proper finite-fiber arithmetic surjection. The latter is not yet an injectivity or analytification theorem; new injectivity drafts are outside this review.

No Baba–Granath-style degree-four-map-to-isomorphism shortcut was found in these bounded reads. This is not exhaustive acceptance of every mathematical claim or of the unfinished full theorem.

## Required prose correction

The frozen contact-character packet README used “inertia flips,” while its Lean theorems prove root-sign actions. The earlier independent character review had already recorded that distinction. The [active scope correction](../../../quartics/quartic-318-326/proof/progress/receipts/contact-character-quotients/SCOPE-CORRECTION.md) narrows that wording and the intended “inertia quotients” interpretation. The active progress README links it prominently; original hash-bound artifacts remain unchanged. No ring/field theorem or inverse map failed.

## Execution and next work

Hosted [run 42450454824](https://github.com/doublemover/diophantine-z-q/actions/runs/42450454824) passed all 50 jobs and the full recursive audit of 20,034 declarations from 1,083 modules. It reused exact-source CI artifacts and ran the combined audit freshly; it was not a clean rebuild. Source review and execution evidence are separate.

These bounded checks support resuming the existing forward proof lanes while keeping the remaining actual PEL/metric realization, global group-law construction, arithmetic witness existence, and final assembled proof review explicit. Unrelated final-publication retrieval and the separate discriminant-six numerical orientation issue are not silently declared solved and do not postpone the distinct discriminant-210 work.
