# Native norm, universal obstruction and exact class consequence

The native integer algebra equivalence maps the actual quadratic basis to the full native integer ring. Algebra.norm_eq_of_algEquiv and norm_eq_matrix_det compute its norm from [[r,-210s],[s,r]], giving r²+210s². This is the actual native algebra norm, and Ideal.absNorm_span_singleton gives the norm of an actual principal ideal as its absolute value. The form is nonnegative, so the native integer absolute-value conversion removes natAbs legitimately.

For arbitrary integer coordinates, suppose r²+210s²=d<210. Nonnegativity of r² forces s²<1. Since s² is a nonnegative integer, it is zero, hence s=0. Therefore r²=d. This universal argument has no bound on the input coordinates. Each of the fourteen listed proper divisors is independently certified nonsquare: any square equal to one of them has -10<=r<=10 because d<=105, then a complete finite integer-case proof rejects all possibilities.

If an actual native ideal of norm d were principal, choose its native Submodule.IsPrincipal generator, pull it through the actual full integer-ring equivalence, and apply the produced norm formula. The universal obstruction contradicts its norm. Apply this to the exact native reduction ideals already constructed for all fourteen divisors, whose norms were proved from their literal quotient ring equivalences. Finally use ClassGroup.mk0_eq_one_iff on the original four nonzero ideals to prove their actual native classes are not one.

This does not yet identify products of different prime ideals or exhaust the native class group. Those require separately produced ideal-product equalities and Minkowski classification. No arithmetic Galois action is substituted for the analytic labels.
