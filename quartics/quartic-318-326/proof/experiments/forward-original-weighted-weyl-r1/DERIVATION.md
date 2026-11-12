# Derivation and consumer identity

1. Write Q_k(x)=x0²+x1²-x2²-x3²-k*x4² and B_k(h,y)=h0*y0+h1*y1-h2*y2-h3*y3-k*h4*y4. Ring normalization proves Q_k(y+h)-Q_k(y)=Q_k(h)+2B_k(h,y), for every integer k, including zero.
2. Fourier phases have period one and positive exponent. Conjugation negates frequency. Thus e(Q(x))*conj(e(Q(y)))=e(Q(x-y))*e(2B(x-y,y)). There is no normalization factor.
3. Expand S*conj(S) over s×s. The actual image of (x,y)↦x-y contains every summand, and finite fiberwise summation partitions exactly this product. We retain w(x)*conj(w(y)) inside each fiber. Triangle inequality and unit phase norms give |S|²≤sum_h |C_h|.
4. actual_weight_finite_support constructs a finite support from W(B^-1 x), independent of theta. actual_circle_eq_finite identifies the result with the identical scaledCircleSum used by minorArcIntegral. No count, support, weight or normalization is replaced.
5. Separately, rectangular unweighted original boxes factor into five one-dimensional quadratic sums with coefficients 1,1,-1,-1,-k. This assertion has a narrower weight domain than step 4. The missing transfer is explicitly not assumed.
6. On an interval m,...,m+N-1 the linear phase is e(cm)*e(c)^j. Induction proves (z-1)sum_(j<N)z^j=z^N-1 even at z=1. For z!=1, unit norms bound the numerator by 2 and the positive denominator justifies division. Triangle inequality also gives N. At resonance the exact value is e(cm)*N.
7. The literal one-dimensional quadratic shift has difference c(y+h)^2-cy²=ch²+2chy, so its absolute correlation is bounded by min(N,2/|e(2ch)-1|), except at resonance where the length bound always applies.

The next analytic consumer requires bounds over the actual displacement fibers for the actual weight and minor domain. None of these finite equalities alone supplies this summation, a rational approximation, an o(B^3) minor integral or a prime-producing statement. The inherited hminor hypothesis is unchanged.

Historical disposition: the published309 circle partition and support arguments are preserved. No unpublished Weyl draft was available at implementation time, so comparison with its actual argument remains unresolved. This is a new reconstruction, not a priority claim. Manuscript incorporation: pending; no manuscript or acceptance record changed.
