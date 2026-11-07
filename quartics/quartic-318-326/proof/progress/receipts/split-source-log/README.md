# Literal split-source logarithm integration

This packet maps the literal source curve into the actual split p-adic curve and proves actual logarithm-domain membership, using the constructed additive logarithm rather than an assumed formal-log interface.

## Checked interfaces

- `SourceSplitLog318.valuation_embedding`: the actual ring embedding induces exactly the previously constructed normalized split valuation.
- `SourceSplitLog318.source_H_log`: from the literal source and a split H contact of depth at least 8, constructs actual formal-subgroup membership for mapped H and an integer logarithm depth r at least 4.
- `SourcePrimarySplitLog318.source_primary_log`: every literal primary reciprocal point is a member, including its identity branch and either sign of its ordinate. It has the exact parameter relation z(U_i) = phi(L_i) z(H), and its logarithm valuation equals the literal z valuation.
- `SourcePrimarySplitLog318.source_split_log_data`: one shared actual logarithm subgroup contains H and all four primary points, with v(fH) = 2r and v(log H) = r at the same r.

The retained hypotheses are the literal source equations, a specified split root rho with rho^2=2, p prime and at least 19, the good-contact exclusions (including 41), H depth at least 8, and primary leaf depths at least 2. These are the exact source contact data already delivered by the separate place-selection packet. This packet does not assume or assert that the formal-parameter ratio equals the logarithm ratio; the analytic error transfer remains a separate composition.

## Verification

Run `bash run.sh`. Both modules are compiled with `-Ddebug.skipKernelTC=false`. The full recursive axiom audit checks every declaration recorded in the two modules, including generated auxiliaries, and permits only propext, Classical.choice, and Quot.sound. Current result: 26 declarations, two modules, no additional axioms.

No repository files or PRs are changed. Source and directly imported project dependencies are hash-bound in the receipt.
