# Bad-7 regular subgroup and actual finite-place signs

Strict-kernel checked Lean 4.35.0 packet, Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679.

Main theorem: BadSeven318.all_multiples. For every actual NumberField.FinitePlace K with w(D)<1, every integer n satisfies 1 <= w(((n • P).xRep) 0). Here K is the project's actual Q(sqrt(2)), D=(3-sqrt(2))^2, P is the literal LocalGenerator318.P, and xRep(0)=1 for the identity.

The proof does not assume a reduction homomorphism, a place-identification theorem, an analytic logarithm, or a reciprocal square root. RegularCusp318 proves a nonarchimedean Vieta obstruction: two intersections with x absolute value >=1 cannot have a third intersection with x absolute value <1 when |D|<1. RegularCuspGroup318 attaches it to actual Mathlib short-curve addition, including secant, tangent, inverse and identity branches, and constructs the genuine regular AddSubgroup. BadSeven318 proves |3-sqrt(2)|<1, |7|<1, |2|=|3|=1 and |x(P)|=1 directly at each actual finite place before applying subgroup closure.

The three project modules were freshly compiled with debug.skipKernelTC=false. BadSevenAudit318 recursively audits all 20 declarations in the three modules, including their full axiom dependencies. Only propext, Classical.choice and Quot.sound are permitted. No custom axioms or proof placeholders occur.

Replay: bash build-all.sh. The run-one.sh script names the pinned workspace toolchain and existing height-work, soundness-local, padic-tail and lean-audit proof dependencies. This is a three-module supplement, not a duplicate archive of those already-built dependency packets. All source files, per-module logs and source/log hashes are included. No binary outputs are archived.
