# From literal bin sum to native logarithm and actual full-sum consumer

## Complete finite partition
For q>0,[-q,q] is the disjoint union[-q,-2] union{-1,0} union[1,q]. The proof includes q=1,where the negative tail is empty. Both central bin costs are exactlyN. Positive bins have costq/b. For negative bins b<=-2, the denominator is -b-1,not |b|. The injective map b↦-b-1 has image inside[1,q]; nonnegative summation bounds its complete contribution by the positive reciprocal sum. Thus the upper bound is2N+2q*sum_{b=1}^q1/b. The endpoint asymmetry is enlarged honestly,not discarded.

## Exact native harmonic identification
The integer positive sum is matched by explicit finite bijection n↦(n:Z) from Icc1 q.toNat,with all nonnegative/cast bounds proved. Native harmonic_eq_sum_Icc and Rat-to-real sum/inverse casts identify this with(H(q.toNat):R). Positivity of q gives(q.toNat:R)=(q:R). The pinned native harmonic_le_one_add_log theorem applies with exactly this index and real logarithm,producing2N+2q(1+log q). Nonnegativity of the new logarithmic budget follows also from the existing nonnegative bin budget and the proved inequality.

## Actual downstream consumption
Multiply the logarithmic inequality by the nonnegative complete block count16H/q+2. This removes the finite bin sum from completeEvenKernel(H,N,t) for the same rational error|t-a/q|<=q^-2 and coprimality hypotheses. Apply it at radiiH and|κ|H with the same original N. The r13 complete five-kernel bound and nonzero signed coefficient injection then yield the explicit logarithmic bound for scaledCircleSum itself,not an isolated line or assumed aggregate. All constants and original weights/coefficient signs remain fixed; no additional approximation premise is smuggled in.

## Limits and verification
A pointwise rational Weyl bound is not by itself the integrated minor-arc theorem. Actual minorDomain denominator/error/distribution choices and any needed refined estimates,moments or integration remain open. The exact finite regression checks partitions,injections,harmonic budgets and complete rational centered-distance kernels. It also checks a rational128-term positive atanh-series expression as a sanity lower surrogate for log; the transcendental log theorem is supported by the native primary proof,not inferred from the regression. No compact-smooth witness,Lean elaboration or final asymptotic is claimed by finite tests.
