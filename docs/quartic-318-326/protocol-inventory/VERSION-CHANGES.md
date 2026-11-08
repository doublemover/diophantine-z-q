# Version 11 to Version 13: actual changes and contribution impact

The current upstream manuscript is **Version 13**. Version 11 remains the historical source of the Kato index/norm/class repair, not the intended final baseline for this contribution.

## Version 12

The exact TeX comparison has four change blocks: title, abstract, revision summary, and a new 972-line section. It retains the earlier mathematical body and reduces the 523-variable baseline to:

- 498 total variables, 497 witnesses, 467 quadratic residuals and 24,669 quartic monomials, using fixed symbolic integer coefficients.
- 514 total variables, 513 witnesses, 483 residuals and 24,716 monomials, with fully written decimal coefficients.

The new proof uses mixed orders 12/40, normalized detector poles, five half-trace guards, a one-coefficient anchor, a shorter scalar norm tree, a reciprocal chart, mixed toric circuits, denominator cancellation and norm-coordinate reuse. Its 25-application inventory and independent decisions retain the earlier arithmetic inputs. A later serialization repair makes generated UTF-8/CRLF files reproducible across platforms; it does not alter the mathematical tables or manuscript.

Sources: [Version 12 guide](../../manuscript-revisions/version12/README.md), [inserted proof](../../manuscript-revisions/version12/addition.tex), [application inventory](../../manuscript-revisions/version12/inventory/APPLICATIONS.json).

## Version 13

The exact TeX comparison with Version 12 again has four change blocks: title, abstract, revision summary, and a new 861-line section. It adds reductions from 498 to:

- 394 total variables, 393 witnesses, 364 quadratic residuals and 6,338 quartic monomials, with fixed symbolic integer coefficients.
- 411 total variables, 410 witnesses, 381 residuals and 6,388 monomials, with decimal coefficients of magnitude below 2^3247. The complete table is 214,957 bytes.

The new proof includes order-10 transfer, odd-norm/identity/reciprocal charts, squared-output biquadratic maps, the enlarged auxiliary H domain and half-index/torsion argument, two modular no-root certificates, parity-sensitive deterministic correction, a depth-24 norm, simultaneous real and finite-place preparation, CRT/preparation zero, pole normalization and noncircular anchor rescaling. The decimal companion adds sixteen repeated-squaring coordinates and a separate C*tau coordinate so the rescaled anchor remains quadratic.

The 39-application inventory records 351 obligations, seven component transports and 97 changed residual objects. Its structural validation and internal model decisions are distinct from a completed formal proof and do not re-prove the retained restricted-converse, height or prime-pattern theorems.

Sources: [Version 13 guide](../../manuscript-revisions/version13/GUIDE.md), [inserted proof](../../manuscript-revisions/version13/addition.tex), [inventory scope](../../manuscript-revisions/version13/README.md), [394/411 package](../../../quartics/quartic-394-411/README.md).

## What this changes for 318/326

- Use Version 13 as the active manuscript, with exact current passage bindings. Preserve the Version 11 repair and its decisions as historical evidence; do not relabel their hashes.
- Both later editions preserve the earlier mathematical body, including the repaired Kato construction, apart from line shifts. This supports a bounded carry-forward comparison, not automatic acceptance of every changed consumer.
- The upstream 394/411 reductions are a different composition from the contribution's 318/326 construction. Their acceptance cannot discharge the contribution's actual simultaneous 288-row witness assembly or geometric realization.
- The current merged research protocol is version 1.1. Its requirements concern complete source/application inventories, exact non-author decisions, all recorded objections, and final closure. Protocol versions and manuscript versions are different sequences. An open protocol-1.2 proposal is not treated as an already merged requirement.

The finite 498/514 and 394/411 reproductions passed after the upstream merge. That is computational evidence, not independent arithmetic closure. No pull request is being created.

## Separate reuse assessment

This is a list of candidate comparisons, not a claim of additional savings.

1. **Private-coordinate and shared-reciprocal elimination is reusable in principle.** Version 13 gives explicit forward/backward maps fixing outside coordinates. Compare their incidence and nonvanishing premises with the actual 318 residual list before importing a transformation. Savings cannot be added across overlapping coordinates.
2. **The rational logarithm replacement is worth comparing later.** Version 13 proves the rational function's denominator and numerator nonvanishing on its actual point domains, its real bounds, and its formal precision. The current 318 construction uses different detector orders and final scalar data. Matching a power-series truncation alone would not justify replacing its logarithm circuit.
3. **Identity-inclusive and squared-output charts may offer local reductions.** Their zero branches and exterior projection equivalence are explicitly proved in Version 13. Applying them here requires retaining the same scalar/root points, all guards and the simultaneous completeness construction, rather than merely matching curve equations.
4. **Do not count existing shared techniques as new savings.** The 318/326 package already has preparation-zero/pole normalization and a smaller fixed-constant companion: seven squaring coordinates plus one product coordinate. Version 13 uses sixteen plus one. Both need the product gate to keep the anchor quadratic when the large coefficient becomes a computed variable.
5. **Parameter-dependent changes are not drop-ins.** Version 13 uses beta=51(2X+1)^2+2504, its own parity correction, order-10/40 tests and depth-24 scalar norm. The literal 318 construction instead uses beta=3723(2X+1)^2, detector orders4/13 and its own scalar/height budgets. Any transfer must recompute the exact local, real, torsion, height and simultaneous-choice implications.

The current 318 count is already below 394, but this does not rule out combining compatible ideas. The appropriate experiment compares actual sources, builds both maps or a new simultaneous existence argument, then re-expands the complete residual list and checks the arithmetic consumers.

**Deferred task requested by the user:** after the current proof and review work is finished, assign one Astra worker at xhigh reasoning to test whether the techniques developed for 318/326 can improve the Version 13 construction further. Keep the experiment separate, preserve the accepted baseline, and make no pull request. It has not been started.
