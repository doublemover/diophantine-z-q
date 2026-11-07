# 318 source-completeness work

This isolated directory contains a source-specific conditional integer-to-witness proof, fresh analytic-dependency review, and new kernel-checked sublemmas. It does not establish the full 318 arithmetic equivalence by itself.

## Mathematical deliverables

- `COMPLETENESS-ASSEMBLY.md`: all 288 raw/final source rows, fixed witness-choice order, coherent signs, quotient domains, current constants, pole normalization, and explicit global assumptions.
- `PRIME-PATTERN-AUDIT.md`: actual v10 analytic proof, source applications, order-separation refinement, and exact validation boundaries. No new mathematical defect found in this pass.
- `BRANCH-CERTIFICATE.md`: special-case ray fourth-power theorem from ordinary quadratic reciprocity, explicit half of R0, and the coherent opposite +1 branch. Narrow independent review passed.
- `ANCHOR-COMPLETENESS.md`: all-place local-global existence for the literal physical anchor, with its affine denominator justified. Narrow independent review passed.

## New kernel-checked modules

- `NormChainCompleteness.lean`: the actual left-deep detector with four unsquared delta leaves; residue dichotomy and trace unit, including zero leaves.
- `OrderSeparation.lean`: Hasse-error/spacing arithmetic excludes all selected-prime divisors of opposite orders.
- `PrimeCRTAssembly.lean`: product/lcm coprimality, compatible primary exponent, arbitrarily large indices, and the real-component compatibility of coherent charts.
- `BranchHalving.lean`: square-root algebra and explicit nondegenerate half of R0, valid over finite residue fields, not just characteristic zero.
- `AnchorLocalCharts.lean`: exact local-chart algebra, finite radicand residue checks, affine normalization and scaling.
- `../prime-witness-bridge/AnchorAnisotropy.lean`: independently implemented integer descent, rational anisotropy, unconditional affine denominator, and physical-anchor output from a homogeneous zero.

`bash verify_local.sh` reruns all six modules and the exact source accounting. The latest run passed. Printed theorem axiom sets contain only ordinary Lean foundational axioms; no `sorryAx` occurs.

## Finite source checks

`check_assembly.py` checks exact Q(√2) chart, compressed-anchor and scalar-minus-branch identities on its stated finite samples, then exhaustively classifies every source row. `row-coverage.json` binds all seven source files by SHA-256 and lists all 288 obligations. This is not a global existence certificate.

## Remaining boundary

PP and RC remain explicit global inputs of this assembly. Their actual manuscript arguments exist and were examined; "remaining" does not mean an absent historical proof or a newly discovered counterexample. The prime-pattern audit found no concrete defect, and the restricted-converse worker closed downstream two-twist/witness bridges but did not close all retained arithmetic producers in its fresh pass. No Lean theorem here derives all source witnesses from fully formal PP and RC producers.

The anchor proof uses standard Hasse–Minkowski after explicit local checks. The branch proof uses ordinary quadratic reciprocity and finite-field cyclicity. These classical inputs are distinguished from the specialized global PP/RC chains and from the algebraic parts now checked by Lean.

## Extended producer validation

The later work is indexed in `AUDIT-PROGRESS.md`. It includes actual detector,
weighted CM/sign-fiber, global theta/Weil, even Shimura–Waldspurger phase,
finite-stage coefficient reading, and bounded rough-companion certificates.
Each subdirectory retains primary sources, exact scope, receipts and any
formal substeps. These extend the original six-module pass above.

`bash verify_all.sh` reruns all 15 listed modules and the 288-row accounting.
The common PP/RC producers are still not fully formalized by these modules.
For the latest *mathematical audit* boundary, use `AUDIT-PROGRESS.md` and the
separate converse worker's current report rather than the older boundary
paragraph above.
