# All-order constants from the same original paired weight

## Finite differences and exact derivatives
mixedDifference f[]x=f(x). For u::us it is mixedDifference f us(x+u)-mixedDifference f us(x). directionProduct is the product of actual step norms, with empty product1. Thus order0 remains amplitude, not zero. An induction on the actual finite list differentiates this expression by native translation/chain/subtraction rules. Its derivative is literally mixedDifference(fderiv f)us x as a continuous linear map, not a scalar surrogate.

## Producing every order
Induct on k with the codomain quantified inside the induction. The base uses compact support and continuity to bound f globally, including outside support. The successor invokes the induction hypothesis on the actual operator-valued fderiv f, smooth by contDiff_infty_iff_fderiv and compact by HasCompactSupport.fderiv. The resulting bound on the derivative of the finite difference is consumed by convex-univ mean value between x and x+u. This adds the exact final factor|u|. The chosen C depends only on f and k, before all points/directions. The Type0 restriction on this generic statement covers the original real coordinate spaces and every continuous-linear-map codomain in its induction; it is not claimed universe-polymorphic beyond that scope.

## Both factors, one compact doubled-space producer
P(x,y)=W(x)W(y) is smooth by actual projection/composition/product APIs. Its nonzero support is contained in tsupport(W)×tsupport(W), compact. Neither W composed with a single projection is incorrectly claimed compactly supported. Translation-uniformity follows from evaluating this ONE global P at(x+h,x), not from selecting a compact support or constant for each h.

The exact finite-list induction identifies mixedDifference(W(-+h)W)us x with mixedDifference P(us.map diagonal)(x+h,x). Because the product space has max norm, each diagonal step(u,u) has precisely norm|u|. This includes all repeated/mixed/zero directions and all cross terms of the two original factors automatically. No separability or dropped translated factor is used.

## Actual complex lattice scaling and finite order family
The existing exact latticePairedWeight identity is transported through finite differences using complex ofReal subtraction and an exact additive-map composition lemma. The scaled original embedding sends u to B^-1*integerEmbed(u); the product of norms is exactly B^-length times the unscaled product for B>0. Hence every order k has a produced actual lattice constant Ck/B^k. A finite sum over Fin6 of nonnegative Ck dominates each Ck, giving one uniform constant for every length<=5. Unit-direction lists then have norm product at most1, so every relevant face/corner/interior order has the needed scale law.

## Downstream boundary
These are the actual increments needed by a future five-dimensional Abel variation consumer, not merely supplied derivative premises. This packet does not yet build that full consumer or claim the required power-saving correlation bound. Existing r10 full two-axis aggregation remains unchanged. Higher-dimensional index accounting, five kernel factors, harmonic/log estimates, minor-domain denominator selection and integrated o(B³) remain open. The finite polynomial regression validates algebra/diagonal/scaling/order conventions only, not compactness/smoothness or analytic constants, and no local Lean was run.
