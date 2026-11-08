# Completed character rank eight

The two new Lean modules prove that every original completed character morphism has rank eight at every target point. The generic helper compares the actual finite-flat Scheme morphism rank with its actual generic-stalk field degree through an affine pullback square and compatible section/germ scalar towers. The consumer applies that result to `CompletedCharacterGlobal318.completedMap i` for all `i : Fin 4` and all `y : Target i`, including branch points and infinity.

Both sources strictly compiled locally on 2026-11-08 with `debug.skipKernelTC=false`. The target-only recursive axiom audit covers 9 declarations in 2 modules and permits only the three standard roots. Independent review and integrated hosted replay are pending. Contact's flatness source is consumed with its separately recorded per-module status; its integrated audit remains a distinct pending step.

No completed model is replaced. No etaleness, ramification index, Jacobian morphism, polarization, PEL identification, or full arithmetic theorem is claimed.

Public whitelist: the two source modules, Audit.lean, MODULE_ORDER.txt, APPLICATION.json, SOURCE-BINDINGS.json, README.md, receipt.json, SHA256SUMS, and the four successful check/audit logs. Local oleans, working revisions and failed elaboration scratch are excluded.
