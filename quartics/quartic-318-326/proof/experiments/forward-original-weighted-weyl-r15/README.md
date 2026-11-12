# Actual minor-domain Dirichlet cover and integrated rational envelope

All 1251 predecessor Lean sources are unchanged. Seven new modules, 392 lines, give 1258 total. Hosted Lean validation is pending; no local Lean, profiling or resource change.

This packet crosses from an assumed pointwise approximant to actual approximation existence and integration. Native Dirichlet gives a reduced fraction a/q with q<=Q and error<=1/((Q+1)q), hence <=q^-2. The original major arcs use actual ZMod unit indices and a shifted Ioc fundamental interval. Constructing exactly those indices proves every reduced q<=N has error>=N/B² on minorDomain. The inequality is weak because left major endpoints remain in the minor set. When 1/(Q+1)<N/B², the produced q is genuinely >N. Q=ceil(B²/N) satisfies this strictly.

The existing modulus-one major arc forces minor points to satisfy N/B²<t<=1-N/B². The same strict width then makes every selected rational canonical: 1<=a<q. Thus the actual minor domain is covered by finitely many measurable intersections with closed rational cells, indexed by N<q<=Q, 1<=a<q, gcd(q,a)=1. The exact cell measure is bounded by 2/((Q+1)q). These cells can overlap; integration uses their indicator sum and retains all multiplicities.

The actual r14 full five-variable bound produces one R,C before B,N,Q,a,q. Its square root is the explicit rationalWeylEnvelope. Cell norm integrals are bounded by this envelope times their actual width, and the full original minorArcIntegral is bounded by the complete finite sum of these quantities. The canonical-Q theorem leaves no Diophantine existence hypothesis for a caller.

This is a real integrated upper bound, NOT yet o(B³) or a power saving. The q^-2 envelope loses the approximation-error dependence, and at the upper denominator range its bound can still be too large. A stronger pruning/error-sensitive estimate or moment argument remains needed. No prime/ray/order/Anchor/rank claim.
