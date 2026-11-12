# All-order actual paired weight control

All1229 predecessor Lean sources remain byte-identical; five new modules give1234 total. No local Lean or resource-budget changes. Hosted kernel validation remains pending.

A generic ordered mixed finite-difference definition is differentiated exactly through finite translation/subtraction. Induction through the ACTUAL operator-valued fderiv of a smooth compact function produces a global order-k constant before all step vectors and base points. Each induction stage uses compact derivative support and the global mean-value theorem; no higher derivative bound is assumed.

For the actual weight, P(x,y)=W(x)W(y) is smooth and supported inside the compact product of the two original supports. Its differences along diagonal steps(u,u), evaluated at(x+h,x), equal the mixed differences of the ACTUAL paired weight W(x+h)W(x). The product max norm gives |(u,u)|=|u| exactly. Constants are therefore uniform in all translations, without tracking h-dependent support or expanding exponentially many Leibniz terms.

Exact real-to-complex and additive scaling identities identify these differences with the original complex latticePairedWeight. Order k scales by B^-k. Finally a finite sum of the six produced order constants gives ONE C valid for every order0..5, every positive scale, every displacement/base point and every list of original directions. For unit coordinate steps the bound is simply C/B^k. Corners/order0, zero steps, repeated directions and negative steps are included.

Remaining: a complete five-axis Abel identity/variation bound consuming these actual all-order increments, full five-kernel displacement aggregation, sufficient harmonic/approximation control over actual minorDomain and integrated o(B³) decay. The r10 whole-sum two-axis bound is preserved but not upgraded to a five-axis bound here. No final minor saving, prime/ray/order/Anchor or rank claim. Exact finite polynomial regression is not a compact-smooth witness or Lean proof.
