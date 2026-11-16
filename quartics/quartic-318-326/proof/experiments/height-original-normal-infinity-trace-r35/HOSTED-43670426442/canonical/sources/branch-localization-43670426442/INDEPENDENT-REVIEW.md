# Independent source review: branch localization scalar dictionary repair

Verdict: narrowly justified direct scalar-associativity proof preserving the actual dictionaries. Future hosted elaboration remains unverified; no local Lean.

APPLICATION2021c0163396d27239b249827e390c8899a48bf78d7e5ebbd9a36fe87cf5ff72.
SOURCE-HASHES9a7397ad8f4fb97e684f5efb98ab60a1f97fa758624989b267387952531cc4b2: all16 bindings independently verified (not the15 in the initial message).
Candidatee907c1b8897b44c5208443d535c72e22daa1716a13a813b0d915314eabef339c; before4ffeebc2c478d3f3e7c369eea8a65123b851e3899e38b7ffd8eadbbda1972e07.
Own current cotangent58 receipt5497f74fa008e6879f463c2cfa8ce1ca49c77946d47d2b864b3dde41780f38fb independently matches frozen intake and exact51-success prefix. Full module FAIL9.992s at84:2; earlier Away/timeout errors absent, not a module pass.

The actual error is that of_algebraMap_smul synthesizes canonical Algebra.toSMul for the coefficient action, whereas the goal uses the native quotient action on A and tensor action on OpenOrder. The candidate avoids that constructor and proves the required smul_assoc directly with those existing actions. It uses the already constructed polynomial tower to express c•a as the polynomial constant algebraMap times a, transports that via the unchanged sourceMap_on_polynomial lemma, and uses multiplication associativity and the actual OpenBase tower to reach c•(sourceMap a*z). Native IsScalarTower.algebraMap_smul has the required arbitrary-module scalar-action form; it is not an unproved replacement of a dictionary.

Read full changed proof, surrounding local instances and named localization equivalence, exact producer context and pinned tower API. The polynomial action is the existing aeval algebra; the quotient complex action remains intact. Only sourceTower's proof body changes. All declarations, inputs, domain, denominator, scalar maps, source and target localizations, prior named helper and options are unchanged. No new helper, external scalar tower, unit premise or source restriction is introduced. Existing transparency/resource options are retained exactly, not increased.

All nine application clauses correctly preserve the whole branch-localization goal and distinguish absent diagnostics from acceptance. Definitional reductions in the initial change, polynomial scalar identity and tensor/OpenBase associativity still require hosted checking. No performance result, all-copy propagation or successor kernel acceptance is inferred by this review.
