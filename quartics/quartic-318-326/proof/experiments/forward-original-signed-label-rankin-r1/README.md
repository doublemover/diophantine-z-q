# Actual original signed-label Rankin producer

All 372 predecessor sources are exact, including the latest rational-denominator normalization repair. Five new modules construct a subpower summatory bound for the coefficient consumed at the FINAL original good-point count. They do not assume a label-average estimate or global weighted Dirichlet summability.

OriginalRetainedFamilyWeight318 identifies familyWeight(kappa,t)=prod_{p retained}(p+1)/M^2 with an actual multiplicative arithmetic function on abs(t). A prime dividing 2*kappa has weight 1, at EVERY positive power; every retained prime has (p+1)/p^2 at every positive power. The zero extension of the arithmetic function is never substituted for an original nonzero label. The same actual integer index M^2 is used, not an abstract replacement lattice or residue count.

OriginalRetainedDirichlet318 defines f(n)=weight(n)*n^(-delta), delta>0. It derives the exact local prime-power series L_p=1+w_p*r_p/(1-r_p), r_p=p^(-delta), from a geometric series and actual multiplicativity. The pinned finite-prime Euler theorem then supplies the sum over integers supported on ANY finite prime set. Only local geometric summability is required; no global Euler theorem with the desired conclusion hidden as a hypothesis is used.

OriginalFiniteLabelRankin318 injects every actual positive label 1<=n<=B into integers factored over the actual prime range <=B. Positivity gives the finite Dirichlet sum bound by the corresponding finite Euler product. The genuine Rankin inequality then bounds the original familyWeight sum by B^delta times that product.

OriginalUniformEulerRankin318 bounds those finite Euler products UNIFORMLY in B. Primes dividing 2*kappa retain their exact full local series in badProduct. Outside that finite set, the excess is <=C_delta*p^(-1-delta), with C_delta=2/(1-2^(-delta)), derived from w_p<=2/p and ratio monotonicity. Pinned real p-series summability and 1+x<=exp(x) bound the actual products by
  rankinConstant(kappa,delta) = prod_{p|2*kappa} L_p * exp(C_delta * sum_{n>=0} n^(-1-delta)).
This is a genuine constructed constant, independent of B. The theorem requires kappa!=0; there is deliberately no uniform kappa=0 assertion because all primes would then be unpenalized. Excluded primes and their arbitrary powers cannot disappear from the coefficient.

OriginalSignedLabelRankin318 uses precisely the existing OriginalGlobalBadMass318.labels B, namely nonzero integers in [-2B,2B]. It constructs the injection into (sign, positive magnitude), proves injectivity and transports the exact same original family weight. Thus
  sum_{t in ORIGINAL labels B} familyWeight(kappa,t)
    <= 2*rankinConstant(kappa,delta)*(2B)^delta.
Both signs and all excluded-prime powers are retained. This is the needed actual label-average producer, not a restatement accepting one as input.

Validation: exact rational checks cover 2400 final integer-index coefficients, 9568 coprime products, 288 prime powers (108 excluded powers), 144 local geometric series identities; 65-digit real regressions cover 252 finite Rankin inequalities, 652 local excess bounds, 252 uniform Euler products and 252 signed label bounds. Exact signed-label equalities are also checked. These finite tests supplement, not replace, the Lean arguments. No local Lean execution.

The source uses the pinned Mathlib revision 56a005855ea17e0b0958f73ec801ae140b0a1679 finite Euler, prime-factor, real-power, infinite-sum order and p-series APIs. Primary-source hashes are recorded below in PRIMARY-SOURCES.json. Independent source review and hosted elaboration remain separate.

Remaining: join this original signed-label bound to the constructed good-point budgets, make their logarithmic height bound uniform over the same labels, restore original source logarithmic weights, and combine with the earlier weighted bad-family tail at T=B^(3/4). Optimized sieve and actual Gaussian prime-pattern production, four rational twist-point pairs and the rational Anchor theorem remain unfinished. This packet does not assert the final quartic theorem.
