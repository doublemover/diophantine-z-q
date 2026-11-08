# Recover the arithmetic source twists

The four modules pass Lean 4.35.0 with kernel type checking enabled and a recursive audit of all 90 declarations. Only propext, Classical.choice, and Quot.sound occur. No sorry, native-decision oracle, new axiom, or unverified field-isomorphism premise is introduced.

- SourceTwistArithmetic318 proves the exact cubic depressions, published A/B coefficient identities, coordinate scales, nonzero discriminants, and literal twist products.
- ComplementSquareclass318 proves that four complementary squareclasses uniquely determine all four original squareclasses, over every field.
- SourceTwistRecovery318 turns actual rational short-Weierstrass coefficient scalings into squareclasses (−14,−6,42,−21).
- SourceTwistFieldEquiv318 constructs quadratic root-scaling equivalences and tensors them to an actual Q(t)-algebra equivalence of the four-root fields. Its final theorem explicitly retains the four published coefficient-scaling hypotheses.

SOURCE_IDENTIFICATION.md gives the geometric argument connecting those hypotheses to the published Jacobians. Its PEL/source-curve inputs and standard quotient/Jacobian steps are not formalized by this packet. Independent mathematical review is pending. The pinned manuscript is unchanged; the existing branch-data argument is acknowledged rather than misclassified as a new repair.

Replay from the workspace root with an exclusive lock:

    flock compile-coordination/heavy.lock bash resumed-source-twists/run.sh

receipt.json records the successful replay and source/dependency hashes. The exact Fraction checker was rerun independently of Lean, and the published Table 3 page was visually inspected. This package does not establish integral good reduction, a global smooth/proper source model, or the final Diophantine theorem.
