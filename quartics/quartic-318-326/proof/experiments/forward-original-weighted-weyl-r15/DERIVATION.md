# Exact approximation, actual domain, and integration

## Historical scope and connecting argument
Read the inherited ActualOriginalMajorArcDomain, RationalArcSeparation, CircleMinorArcIdentity, CompleteLogKernel, and FullFiveLogarithmicBound sources. The previous packet produced a pointwise q^-2 rational bound but explicitly did not produce a minor-domain denominator selection or integrated saving. This packet incorporates the native Dirichlet theorem through the actual arc indices and integral. It does not relabel prior approximation-existence claims as absent elsewhere, nor assert a new historical global obstruction.

## Reduced fraction to original index
For q>0, q<=N, 0<=a<q and IsCoprime q a, convert to natural q.toNat,a.toNat. The Fin N denominator index is q.toNat-1; its original modulus is exactly q.toNat. Native ZMod isUnit_iff_coprime supplies the numerator unit and val_natCast supplies its actual canonical value. Thus the center is exactly a/q, including 0/1.

## Shifted interval and strict versus weak error
Write r=N/B². Existing radius_small proves 2r<1/N under B>0 and (N+1)^3<=B. If t lies in (-r,1-r] and a reduced q<=N satisfies |t-a/q|<r, then a/q>-2r>-1/q and a/q<1. Integer discreteness gives 0<=a<q, so the constructed original major index contains t in its Ioc arc. Consequently every minor point has error>=r for all reduced q<=N. Do not strengthen this to >r: a left endpoint of a nonzero original major arc is a real counterexample.

## Produced native approximant and canonical order
Native exists_rat_abs_sub_le_and_den_le applies to every real t, rational or irrational, for Q>0. Its rational num/den are reduced and den>0. Preserve error<=1/((Q+1)q); q<=Q gives the q^-2 consumer error. If 1/(Q+1)<r then every selected q<=N contradicts the preceding lower bound. Taking Q=ceil(B²/N) makes Q>0 and 1/(Q+1)<r by positivity and reciprocal monotonicity. No measurable choice of approximants is needed.

## Finite cover, not a disjoint partition
The literal modulus-one arc is (-r,r]. Its removal forces every minor t>r, while the fundamental upper bound remains t<=1-r. A selected approximation with error<r therefore has 0<a/q<1 and integer 1<=a<q. Define rationalIndices by filtering [N+1,Q] x [1,Q] for a<q and IsCoprime q a. Every actual minor point belongs to its reduced rational cell. Each cell is minorDomain intersect [a/q-1/((Q+1)q),a/q+1/((Q+1)q)], measurable and finite; measureReal_mono gives width <=2/((Q+1)q). No totient/numerator multiplicity or overlaps are removed.

## Full original integral consumer
The r14 theorem produces R,C once from nonzero kappa and smooth compact W. Define the nonnegative envelope to be the square root of its literal full five-kernel expression. On every cell, the strong error implies q^-2 and the original norm-square estimate gives norm<=envelope. Native norm_setIntegral_le_of_norm_le_const yields the integral of the norm over that cell <=envelope*measure, then <=envelope*width.

For a finite measurable cover by subsets of a measurable s and integrable f, norm f <=sum of cell indicators times norm f on s. All summands are integrable on s. Integrate this inequality, exchange the finite sum, and use s intersect cell=cell. This proves norm(integral_s f)<=sum integral_cell norm f without disjointness. The original scaled circle sum is continuous from the inherited compact support producer, hence integrable on the actual bounded minor domain. Apply the cover theorem and every cell estimate to obtain the stated full minorArcIntegral upper bound, at general valid Q and then at the explicit canonical order.

## Remaining analytical work
The finite integral bound preserves every denominator/numerator contribution but is not asserted asymptotically sharp. With Q of size B²/N, the q-only Weyl envelope at q near Q can be too large; stronger approximation-error sensitivity, pruning or moment control remains to prove normalized decay. Merely invoking the displayed finite upper bound does not prove o(B³). Regressions check finite arithmetic, endpoints and overlap integration, not smooth constants or Lean elaboration.
