# Exact five-branch orbit count

Strict-kernel PASS: eight public theorems, twelve recursively audited declarations, one module; standard axioms only.

The input is an actual finite group action on the finite ramification-point set, with group cardinality16 and exponent2; faithful zero-constant formal-coordinate actions on each actual stabilizer; characteristic different from2; every point has a nonidentity fixer; four distinct labeled involutions each with an injection of eight fixed points; and the exact genus5/degree16 Riemann–Hurwitz equation.

The proofs derive, rather than assume:
- each actual stabilizer has cardinality2, from the checked averaged-parameter/compositional-inverse theorem;
- every ramification orbit has cardinality8;
- each point has exactly one nonidentity fixer, so different involution fixed loci are disjoint;
- the actual sum of nonidentity fixed-point cardinalities equals the ramification-set cardinality, via an explicit bijection of fixed-point incidence pairs;
- the four eight-point loci force at least32 ramification points;
- the exact Riemann–Hurwitz equation forces quotient genus0 and40 ramification points;
- the actual orbit quotient has exactly5 elements, via Mathlib's orbit decomposition and orbit-stabilizer equivalence.

Final theorem: `FiveBranchCount318.actual_five_branch_values`.

This is the source-specific finite group-action part of fiber-field-bridge/FIBER-PRODUCER.md §§1–2. The actual smooth curve, full ramification locus, completed-local-ring identifications and faithful action, Riemann–Hurwitz theorem application, and the four original genus-one quotient fixed-locus realizations remain geometric inputs. The packet does not construct Shimura curves or infer all geometric premises merely from an abstract finite action. The branch-label product/rationality and quartic-j identification are separate already described applications.

Dependencies are frozen formal-stabilizer-bridge and tame-formal-coordinate-bridge. Replay with bash build.sh. No repository/Git edits.
