# Original bounded dual incidences and actual exceptional lattice family

All288 unchanged predecessor sources are byte-identical. Three new sources construct a quantitative integer-dual count. One inherited source receives only the exact missing public import identified by hosted Lean.

NonzeroMultipleBox318 bounds the actual ORIGINAL integer coordinate box with all three coordinates divisible by d, excluding zero. If d>B the set is empty, proved by integer divisibility and absolute value. Otherwise an injection into three actual residue intervals gives card*d^3<=27B^3, hence d*card<=27B^3. The latter uniform theorem includes B=0 and every d>0. No lattice minimum, reduced basis or primitive-vector assumption is used.

OriginalBoundedDualSum318 constructs the actual zero-reduction subset of retained DISTINCT primes and proves its product divides all three original coordinates using the exact CRT divisor theorem. It explicitly overcounts the genuine zeroModulus factor by all prime subsets whose products divide the coordinates. Swapping finite sums and applying the nonzero-multiple count gives sum_v zeroModulus(v)<=2^omega*27B^3. Combined with the already constructed actual integer-lattice incidence theorem, this yields

  sum_{0!=v in [-B,B]^3} #Incidence(v) <= 27*4^omega*B^3.

OriginalShortDualLattices318 defines the actual original lattice parameters for which some such nonzero original integer vector annihilates the entire integer lattice modulo the original squarefree modulus. Choosing a witness injects this UNION into the incidence sigma type, so the same bound holds for the number of actual lattice parameters. It does not assume witnesses unique or substitute a projected lattice.

## Geometric boundary
The normalizing factor v/M and its exact membership in the Euclidean dual have not yet been constructed, and no theorem connecting a large third successive minimum to such a bounded nonzero annihilator is supplied here. Thus this is a genuine bounded-integer-dual exceptional-family estimate, NOT yet the BHB successive-minima tail or a quantitative weighted-sieve remainder. Original kappa, the literal R=kappa*w^2-x*z bridge, odd-modulus cancellation and original integer coordinates stay unchanged.

## Exact hosted repair
Hosted run42760115355 on788315c7 passed the previous OvalFlowAddition function normalization and failed only because HasDerivAt.prodMk was unknown. The pinned Mathlib.Analysis.Calculus.Deriv.Prod defines that exact theorem at lines52-54. OvalFlowAddition318 now publicly imports that module; no derivative statement, proof body, heartbeat or inherited mathematical source otherwise changes. The primary source and exact diagnostic are included.

Validation:240 nonzero multiple-box counts,42 actual exception-factor sums,168 full incidence sums,96 actual short-dual lattice unions,28476 zero-subset divisibility checks, plus zero-vector and repeated-prime negative controls. Static292/222 closure/source policy. No local Lean compile.
