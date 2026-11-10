# Explicit first-order local-sieve estimate outside a fixed finite set

## Source and scope

Read the original finite-field-count lemma and its claimed g(ell)=(k+2chi(ell))/ell+O_k(ell^-2) following(eq:v5-local-g) in quartics/quartic-318-326/docs/sources/quartic_v10.tex. The249-source predecessor constructs the exact original density and its integer-residue application. This successor proves an explicit error constant and constructs the fixed exceptional set itself. It does not infer a global prime-pattern theorem from local densities.

All249 predecessor Lean files are unchanged, including the exact hosted pole-chart repair and the four density modules. Two new modules are supplied.

## Exact remainder and uniform estimate

Write q for field size, k for the original coefficient count and e=chi(−1), with e=±1. The exact previously constructed density satisfies

g−(k+2e)/q = −R/[q(q+1)(q²+1)],

where R=(2e+1)kq²+2e(q+1)+k. This identity is checked by clearing the positive denominators in each sign case. For q>1 and k≥0, the proof bounds |R| by4(k+1)q², while q(q+1)(q²+1)≥q⁴. Consequently

|g−(k+2e)/q| ≤4(k+1)/q².

The sign cases retain the actual e dependence in the leading term. No nonprincipal-character contribution is discarded. FiniteSieveFirstOrder318.actual_error applies the estimate to the literal cardinality ratio, using the actual quadratic-character dichotomy and finite-field size positivity.

## Construct the fixed exceptional set

For the original distinct integer coefficientsγ_i and nonzeroκ, form the positive integer

2*abs(κ)*product_(i≠j) abs(γ_j−γ_i).

The product ranges over the full original ordered index-pair set. Duplicate differences are harmless; no required pair is omitted. Its positivity is proved from actual integer distinctness and nonzeroκ. Define the exceptional set as the finite set of prime divisors of this integer.

Every prime outside this set differs from2, does not divideκ and divides none of the original coefficient differences. Integer divisibility is converted to natural absolute-value divisibility by an explicit quotient witness. Every factor is proved to divide the actual product; the prime-factor membership criterion then proves all exclusions simultaneously.

FixedSieveExceptionalPrimes318.outside_density_error uses these constructed conditions, the original residue-injectivity theorem and exact integer distinguished coefficients to obtain the local error bound at every prime outside this one fixed set. This is the quantifier/domain coverage needed before any later asymptotic limit: the exceptional set depends only on the fixed original coefficients andκ.

## Validation and remaining boundary

Exact rational checks cover4284 parameter/sign cases, including q close to1, k0 and both character signs. Fixed-set checks cover24 signed integer coefficient systems and547 outside-prime applications; omitting coefficient-difference factors produces a genuine residue-collision negative control. All249 inherited sources are byte-identical; static source policy and dependency closure are checked. No local Lean run.

The remaining analytic stage still needs the original primitive weighted congruence count, medium/large-prime obstruction estimates, fixed-field Gaussian-prime/Artin/nilsequence/transference results and final order-of-limits construction. The local estimate alone does not establish them. Global rational twist realizations and rational Anchor also remain separate.
