# Exact fourth moment to actual five-coordinate rectangular integral

## Existing source and new connection
Read actual IntegerFactorPairs, DivisorSubpower, TernaryLevelCount, bad-fiber summation and interval/square bounds. The existing signed factor-pair injection and produced divisorConstant(delta) are reused, not postulated as a new divisor asymptotic. The preceding r15 rational cover gives a valid but possibly oversized pointwise-envelope integral. The present moment route seeks to avoid paying five pointwise factors.

## Signed square-difference fibers and the zero stratum
SquarePairs(H,n) contains every original bounded pair with x²-y²=n. The map to (x-y,x+y) lands in Pairs(2H,n) and is injective by the two sum/difference equations. It is deliberately NOT an equivalence: parity may exclude signed factor pairs. For n nonzero, the existing signed divisor code bounds the fiber by 2 tau(|n|). For n=0, x=y or x=-y; a sign flag and y form an injective code into Bool times Interval(H). Thus the zero fiber is <=2(2H+1), including H=0.

Energy(H) consists of every quadruple with x²-y²=z²-w². Its exact sigma equivalence fibers over the first pair. All differences have absolute value <=H². The nonzero fibers are <=2 divisorConstant(delta) (H²)^delta by the existing all-nonzero-integer divisor-subpower theorem. The number of zero base pairs and the size of each zero fiber are BOTH <=2(2H+1), so their total is <=4(2H+1)². The generic bad-fiber sum permits good budget on all (2H+1)² base pairs and adds that zero cost. This gives exactly momentBudget. No zero level is inserted into the nonzero divisor formula.

## Exact Fourier energy, not approximate numerical integration
For a finite frequency sum S(theta), S times conjugate(S) is the full pair-frequency sum with frequency f(x)-f(y). Complex.mul_conj and normSq_eq_norm_sq identify this with the real norm square cast to complex. Integrating finite characters against normalized Haar of period one kills exactly nonzero integer frequencies and counts all collisions with their original multiplicity. The real/complex integral conversion is exact. Applying the second moment to the full pair-frequency sum gives the quadratic fourth moment. No distinct-frequency assumption is made; repeated n² frequencies must remain counted.

For any subset s of [-H,H] and nonzero integer c, an actual collision c(x²-y²)=c(z²-w²) cancels c and embeds into Energy(H). This includes all signs and arbitrary nonzero coefficients, without gcd or primitivity restrictions. c=0 is NOT cancelled. The cardinal injection and energy bound produce the uniform fourth moment.

## Shifted interval and four moments plus one supremum
Native AddCircle.intervalIntegral_preimage and volume=1*haar identify the full circle moment with EVERY real Ioc(v,v+1). Nonnegative integral monotonicity then gives the same bound on any subset of that interval. All quadratic sums and their fourth powers are continuous and integrable on the bounded interval, so no divergent-integral convention is used.

The elementary inequality 4abcd<=a⁴+b⁴+c⁴+d⁴ follows from the squares (a²-b²)², (c²-d²)² and (ab-cd)². Applied to four norms, and multiplied by a nonnegative bound M for the fifth norm, it gives pointwise domination by M/4 times the sum of four fourth powers. Integrate using the actual continuous integrability and four uniform moment bounds. The result is M*momentBudget, for different original bounded subsets and signed coefficients.

## Original downstream identity and limits
The unweighted original rectangle is exactly the product of the five quadratic sums with coefficients 1,1,-1,-1,-kappa. This follows from the literal original quadratic equation and five-coordinate product sum, not from a factorization of W. Apply the moment theorem to the actual shifted minorDomain with its exact measurable-set and interval inclusion. Thus the original rectangular minor integral has a proved four-moment/one-supremum bound.

For arbitrary smooth nonseparable W, integrated multiaxis Abel still must carry mixed differences and actual prefix rectangles through this bound. A pointwise supremum over prefixes cannot simply be moved outside or inside the fourth-moment integral. The finite regression includes a counterexample to that invalid interchange. The useful fifth-factor supremum and compatible major/minor scale choice remain to be supplied before normalized decay. No final o(B³) is asserted here.
