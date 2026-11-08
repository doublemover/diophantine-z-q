# Detached progress-verifier repair: bounded independent review

Decision: accept the exact five-file repair bound in SOURCE-BINDINGS.json. No blocking issue found. This is an independent source/application read, not an independent replay or a hosted-success claim.

## Exact failure and correction

The retained hosted attempt reached progress-manifest after runtime setup and the finite/unit steps. Its old wrapper hid the child output. The retained local reproduction identifies ModuleNotFoundError: check_lean in the detached copied verifier. These are distinct evidence levels: the precise import exception is established by the reproduced child log, not invented from the old hosted log. The repair uses the original repository entrypoint and shared code_only parser while supplying the actual copied progress directory through --root. The default remains the repository progress directory.

I read the full verifier and its actual caller. Every manifest, order, module body and CheckpointAudit read is relative to the selected root. Source hashes, private-inclusive audit selection, closed/topological imports, strict source-policy checks and the Python optimization guard remain in force. The selector does not select an alternate policy or bypass the shared parser. The current finite replay passes the detached copy, not the original source directory. It retains all other finite checks, historical consumer bindings and frozen receipts. The explicit final message still says that this command does not rebuild Lean and sourceArithmetic remains a hypothesis.

## Regression and operational coverage

The two new tests exercise an actually detached fixture without a scripts directory: valid selected data passes; mutation of the copied body fails its hash; a rebound copied kernel override still fails admission; a copied audit override fails too. The existing default-entrypoint, optimized-Python, source-escape and private-audit tests remain. The test checking caller strings is a supplementary routing guard, not a substitute for the detached subprocess tests or actual finite replay.

The wrapper closes its child log before reading it and rethrows CalledProcessError after displaying the exact output. The workflow adds relevant dependency triggers and a failure-only, attempt-qualified seven-day log artifact. The artifact action remains pinned. This improves evidence retention; it does not promise an artifact when setup fails before any log exists, nor does it suppress the failed check.

I read the producer's retained complete finite replay PASS, copied 1,386-module manifest PASS, seven integration-test PASS, fourteen tooling-test PASS, eleven experiment-test PASS and empty actionlint diagnostic log. These are producer executions, not reviewer executions. The unchanged experiment plan still contains only forward-period-projection-r2 and the same proof snapshot/base keys. I checked all receipt hashes and exact equality of the retained patch with git diff. Only the five stated files changed; no Lean body, compiler pin or proof-cache checker was modified.

## Boundaries

The earlier broad CI review remains unchanged. This addendum records the newly exposed copied-package regression and its bounded remedy; it is not a claim that the older review had exercised this path. I authored none of these five patch files and performed no shared edit, full finite replay, Lean compilation, publication or workflow dispatch. I did provide prior independent tooling review and coordination. New hosted validation of this repair remains pending. No arithmetic, analytic, Jacobian or PEL conclusion is added.
