# Where the 318/326 proof stands

This is a reading guide to [research snapshot `ef62acc1`](https://github.com/doublemover/diophantine-z-q/commit/ef62acc1daedef712fb72e520bc271c1b0494c29). **The original Diophantine problem is not proved.** The two advances below concern different objects: a regular arithmetic model is not a rational point, and a locally soluble class need not have a rational lift.

## Geometry: all ordered dyadic twist types

For the four fixed contacts and arbitrary nonzero rational twist coefficients, the [model construction](dyadic-complete-cover-index/README.md) gives a proper, flat regular arithmetic model over the integers that preserves the original generic function field and parameter map. This is a reviewed paper proof, not a Lean theorem. The [256-row table](dyadic-complete-cover-index/cover.json) selects one of 22 terminal arguments per type; the [proof map](dyadic-complete-cover-index/proof-map.json) binds 30 mathematical sources, including supporting arguments. The [independent review](dyadic-complete-cover-index/REPORT.json) distinguishes regularity of the total space from smoothness of its fibres.

To verify the enumeration and all linked source hashes in a checkout, run `python3 check_cover.py --verify-sources` from `dyadic-complete-cover-index/`.

## Arithmetic: one original indexed twist has exact rank one

At the explicit common index in the [indexed calculation](indexed-free-first-twist-rank-one/README.md), with integer input 0 (also −1) and free parameter 18, the **first** curve has rational rank one and trivial 2-primary Tate–Shafarevich group. On the **second** curve, the specified Selmer class is everywhere locally soluble and is not the Kummer image of a rational torsion point; the calculation determines only the stated restriction of its 2-Selmer group. A rational lift of that class would give the required second ordinate. Neither that lift nor the second curve's rational rank follows. See the [independent arithmetic review](indexed-free-first-twist-rank-one/INDEXED-FREE-RANK-ONE-REVIEW.json) and the [preceding same-parameter construction](prescribed-pole-coherent-selmer/README.md).

## What was checked by Lean

The [hosted selected job](https://github.com/doublemover/diophantine-z-q/actions/runs/44328209839/job/134887658127) strictly compiled two geometry components: [principal opens](https://github.com/doublemover/diophantine-z-q/blob/f75d6b7db70ea54feffb1337a59a0c451c7ccb92/quartics/quartic-318-326/proof/experiments/height-original-ks-lattice-assembly-r76/ProperRegularPrincipalOpen318.lean) and [dyadic sign coordinates](https://github.com/doublemover/diophantine-z-q/blob/f75d6b7db70ea54feffb1337a59a0c451c7ccb92/quartics/quartic-318-326/proof/experiments/height-original-ks-lattice-assembly-r76/DyadicSignCoordinates318.lean). Its audit covered 10 declarations; 259 other packet modules were unselected. This job verifies neither full theorem above. The [earlier 62-folder catalogue](README.md) is a historical source index, not a compilation record.
