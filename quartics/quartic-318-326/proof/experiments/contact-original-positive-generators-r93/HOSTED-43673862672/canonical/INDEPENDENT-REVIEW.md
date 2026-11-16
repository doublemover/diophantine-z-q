# Original line section equivalence beta-redex repair

Source/current-contract PASS for hosted checking, not Lean acceptance.

Final BINDINGS891c37873ee54368c1b6c6e8003dbb44ce5744076c0f44cb853bc25ebbf8b172: all10 file references verified. Candidate7dfe9c7859981c59a2b07e06adb1b9db7585e0e6f9900b8db7af2df3817c8e1f. Exact source diff and current sole error read.

The four original restriction/equivalence rewrites are retained. Their residual goal is coordinates(finiteRestriction a)=coordinates(infinityRestriction b). Existing ha and hb have these same terms applied through explicit lambdas, each equal to the same ambient vector z. ha.trans hb.symm supplies precisely this equality by definitional beta reduction, rather than demanding syntactic rewrite matching. No other source, import, public statement, instance, option, scalar, chart or domain change.

The whole matching-space surjectivity still uses actual finite and infinity whole sections, their exact shared full-overlap coordinates and original two-open sheaf gluing. No dimension-only surrogate or new compatibility premise. The final equivalence remains the same matchingLinear map.

Own positive86 run43673862672 records76 successes, including TwoOpen2.522s, then SectionEquivalence failure8.339s. Removing this reported rewrite obstruction is not a full-module or downstream pass; hosted replay remains necessary. All nine current obligations retained. No local Lean/Lake.
