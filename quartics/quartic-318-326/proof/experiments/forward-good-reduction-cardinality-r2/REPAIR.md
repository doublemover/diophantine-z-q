# Narrow actual zero-ordinate branch repair

Preserve tested203r1 and frozen208r1, plus exact90893838 log/RESULT. At LocalPointDifference318 line159, the same-x inverse branch has proven y₁=0 and y₂=0. The subsequent `subst` commands can consume an earlier signed ordinate equality, leaving the explicit `simp only [sub_self]` unable to progress. Replace only those substitutions by a typed equality of the original two Point.some constructors, using Point.some.injEq and the actual hz/hz′. Rewrite the same actual difference through that equality to zero and use the unchanged subgroup zero-membership proof.

All statements, hypotheses, actual points, local cases and finite1M budget are unchanged. All207 other source files, including the five substantive good-reduction/cardinality modules, are exact208r1 copies. Hosted validation pending; no local Lean.
