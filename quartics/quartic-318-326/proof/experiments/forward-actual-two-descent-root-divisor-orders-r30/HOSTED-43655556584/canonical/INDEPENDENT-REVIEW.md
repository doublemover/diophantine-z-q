# Independent scalar residual normalization review

Source/application verdict: PASS for future hosted checking only. No local Lean.

Candidate SHA256 c44cc1de5f97ce863290e60b73e8052493ffde06de9b08d538237689839049ca; before c90edeea368ad0532c5e7729115511794d72805eac8e0e9f9d6c6305f14905cd exactly matches published descent18 at6b664f8406d512c50432425e3bd616447ff8ad8e. APPLICATION.md SHA2565c6bd4c588089b74f21f42d7dc42781699b93ee0344df0fb1ef01104f298f33f. All7 BINDINGS entries verified, including own RESULT82bf4d4c940ed0bda5552541220b3e7edcdefa10f8d33cff2e13a1d861535ee0 and current intake f98a854d773dac7651a663fcbb7b64014e2146205d5ac4b87d418b415a51e244, equal the published packet's intake.

Read actual log, candidate surrounding Hensel proof and downstream prime cases, exact one-line diff and all nine application obligations. Actual run43655556584 fails this module in1.969s with the sole error goal True ∨ u=0 after derivative simplification; prime-norm diagnostics contain no additional error. That is not full-module acceptance of unaffected declarations, but distinguishes this observed frontier from the prior norm errors.

Changing simp [F] <;> ring to simp [F] <;> ring_nf <;> simp normalizes the existing ring expression then closes the resulting propositional tautology. It does not assume u≠0 or discard the u=0 case. The same arbitrary prime p, actual p-adic u,v, polynomial X²-C v, derivative2*u, strict Hensel bound and actual root construction remain. All public telescopes, actual scalar/pole maps, primes2/3/17, imports and options are unchanged. No new resource/trust declaration or local-square premise is added.

The candidate still needs strict hosted validation. No weighted-lane outcome or all-copy propagation is inferred; future successors need their own exact contracts and predecessor evidence.
