# Completeness assembly for the literal 318-variable source

## Status and source binding

This is a source-specific conditional proof of the direction

> For every integer input X, the final 318-variable source has rational witnesses.

It is not an unconditional validation of the construction and does not prove its converse. The two outstanding global arithmetic inputs are isolated below. In particular, no conclusion here discharges `sourceArithmetic` in the existing final Lean bridge.

Reviewed checkout: `e96c25a48a09034a52c3444cdd515c09720cd19d`. The exact source hashes and an exhaustive 288-row register are in `row-coverage.json`. The checked sources are the pinned `quartics/quartic-318-326/construction/318/build_source.cjs`, its raw, translated and sheared IR files, the current arithmetic supplement, and its two pinned manuscripts. All work in this directory is isolated from the checkout.

The source has 318 rational coordinates, including X, and 288 quadratic rows. There are 238 arithmetic/quotient rows and 50 structural rows. Every row is covered below; the executable coverage check rejects an unclassified row. Coverage itself is not a mathematical proof.

The inherited final completeness argument is present in Version 10, lines 19580–19698. The current supplement already supplies compressed-anchor, guard, branch and real-bound refinements. The main new connecting work here is (i) coherent fixed root signs before prime selection, (ii) the residue/trace argument for the actual left-deep chain with unsquared delta leaves, and (iii) exhaustive final-row assembly with the final 4/13, index-8 constants. These are connecting arguments, not a claim that the historical completeness proof was absent.

## 1. The hypotheses actually needed

Use K=Q(sqrt(2)), d=3−sqrt(2), D=d² and E: y²=x³−Dx. Put

- R0=(1+sqrt(2), 2sqrt(2));
- k=−1+(7/4)sqrt(2), m=39/8−(9/2)sqrt(2);
- P=2R0=(k²,km).

The displayed constants satisfy m²=k⁴−D. P is nontorsion; its 2-adic formal parameter has valuation 3/2, in the logarithm's torsion-free isometry region. This explicit fact suffices for completeness. The stronger assertions that E(K) has rank one or that 2E(K)=ZP are not needed in this direction.

The global hypotheses are:

**PP.** The precise simultaneous Gaussian-prime pattern and reduction-order theorem used in Version 10, including its separation refinement at lines 19639–19678. After fixing finitely many distinct forms u+c_j w², a finite avoidance modulus and arbitrary lower bounds, it supplies positive prime values, arbitrarily large u/w², arbitrary prescribed divisibility of w, the stated Gaussian ray classes, compatible doubling-image orders M−,M+, and separation of the selected primes from M+. The exact order/gcd conclusions used are displayed in Section 6 below. The companion `PRIME-PATTERN-AUDIT.md` traces the actual analytic argument and its published inputs. The finite order-separation/CRT consequences now have new kernel-checked proofs, but the full analytic prime theorem is not claimed as formally closed here.

**RC.** The restricted converse for E_l: y²=x(x−l)(x+3l), positive squarefree l≡11 mod12, together with the standard descent and forward analytic-rank-one results. Its consumed consequence is the preparation-zero pole existence statement in Brox v3 lines 2572–2599, derived from Version 10 `lem:original-seven-simultaneous-realization` and `lem:original-seven-parity-completeness` (lines 7780–7935). It is not the different `hyp:PC` predicate and does not invoke a converse for arbitrary elliptic curves. A separate audit is checking RC itself.

The remaining inputs are standard or explicit local facts: elliptic duplication/addition, formal groups at good unramified odd primes, finite local-index subgroups and continuity, the explicit reduction orders/ray calculation, compact real-group recurrence, and the three-witness semilocal characterization proved in Version 10 lines 10982–11004 using the quaternion algebra (2,3). The companion `ANCHOR-COMPLETENESS.md` now gives an independent direct Hasse–Minkowski proof for the exact consumed anchor, with every local place and its affine denominator checked. They are used with their stated hypotheses below. The global contact-height bound is not used anywhere in completeness.

## 2. Input, scalar point, odd Lucas labels and the anchor

Fix X∈Z. Set T=2X+1, beta=3723T² and

