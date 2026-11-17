# Exact actual elliptic point-production frontier

This is a source/interface audit, not a proof or a new compiler result.

## Objects are distinct

The two-descent elliptic curves are E_l: y²=x(x-l)(x+3l), at l=n and n*theta. The simultaneous construction requires positive squarefree l congruent to 11 modulo 12. Its Weierstrass coefficients are [0,2l,0,-3l²,0], c4=208l², discriminant=2304l⁶, j=35152/9. Thus these curves are non-CM, by integrality of CM j-invariants. The parameter changes the quadratic twist, not j.

The manuscript's quaternion discriminant 210 belongs to the different maximal-level Shimura genus-five curve used for the contact geometry (manuscripts/quartic_v13.tex 6869–6878). It is neither this elliptic discriminant nor a universally chosen Heegner field. All four actual prepared poles lie in (0,17), so positive theta for 1-b/17 is compatible; no signed extension is presently required.

## Exact claimed mathematical route in the manuscript

Lines 1090–1199 state RC for full 2-primary Selmer corank one, including divisible Sha. The argument is: finite 2-Selmer dimension three; actual reduced Cassels–Tate duality; full Selmer corank one; restricted converse; analytic rank one; forward Gross–Zagier/Kolyvagin rank/Sha theorem; actual non-torsion points and the required Kummer classes. Apply separately to n and n*theta.

Lines 2973–2995 specify an imaginary quadratic K with every prime of 2N_E split, excluding Q(i) and Q(sqrt(-3)). The ring-class conductor is coprime to 2N_E D_K; auxiliary inert primes avoid 6fN_E D_K. These are genuine conditions, not consequences of the contact discriminant 210.

## Exact inspected Lean frontier

* SimultaneousProducer gives finite descent conclusions from explicit beta/theta factorization, residue, distinctness and mutual-symbol inputs.
* ActualReducedDuality is explicitly an existential alternating nondegenerate pairing on the actual reduced primary Sha. Its consumer does not construct the pairing.
* ActualRankShaCorankEquation retains that pairing input and yields r+t=1. Rank zero with divisible primary Sha remains possible in this equation.
* ActualCorankOnePrimaryShaCriterion gives `Finite(actualShaPrimary) ↔ Infinite(Point)` under full corank one; it does not prove either side.
* FourInfinitePointConsumer requires actual `Infinite(Point n)` and `Infinite(Point(n*theta))` for all four indices. FourActualShaConsumer instead requires actual Sha-two cardinality one at both twists. Neither is supplied by a finite matrix determinant.
* No concrete fixed-field determinant-to-positive-elliptic-height endpoint was found in the inspected sources. A file named FixedFieldCurrent is merely a Mathlib field-theory snapshot. Existing canonical-height positivity in the progress area concerns the separate fixed generator curve ConcreteG8Domain.E, not arbitrary E_n.
* The pinned `AlgebraicGeometry_EllipticCurve_LFunction.lean` snapshot defines formal Euler coefficients and `LSeries`. It contains no analytic continuation, modularity, RC or analytic-rank-one-to-rational-rank theorem. Do not identify the generic LSeries at the boundary with an analytically continued elliptic L-function without a proof.

## Primary literature comparison

Cornut, *Mazur's Conjecture on higher Heegner points*, pp.1–2, explicitly distinguishes ring-class points from a non-torsion base trace; the latter is tied to a nonzero derivative. Higher-layer non-torsion alone does not supply rational points of infinite order.
https://webusers.imj-prg.fr/~christophe.cornut/papers/mcinv.pdf

Skinner's published 2020 converse has rank-one/finite-Sha and semistability/reduction hypotheses in its stated elliptic-curve corollary. It is not the required full-2-primary-corank-one implication by mere name matching.
https://annals.math.princeton.edu/2020/191-2/p01

## Actionable separation

The finite prepared-pole factorization/support interface and the actual restricted-converse/global-rank producer are separate obligations. Continue strict validation of existing finite descent and prepare their actual inputs, but do not insert `Infinite(Point)`, reduced duality, finite Sha, or an analytic-rank assertion as a newly hidden assumption. The current no-hglobal anchor consumer still retains the four elliptic Realizations explicitly. No global completion or timeline is claimed here.
