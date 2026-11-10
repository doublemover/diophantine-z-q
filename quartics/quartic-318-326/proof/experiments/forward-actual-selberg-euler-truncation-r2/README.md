# Actual Selberg Euler mass and quantitative strict-divisor truncation

Exact434r2 preserved, including the complete original Gaussian large-prime pattern tail and latest literal-row repair. Four modules begin the substantive medium-prime Selberg denominator construction using the actual original local densities and retained primes, not a supplied Euler-mass or moment asymptotic.

FiniteBernoulliEulerMoment318 constructs the probability mass on the actual finite Boolean selections, proves its total is1 by finite product expansion, and proves its exact first moment is sum_i q_i*l_i. It then proves finite Markov truncation with STRICT cost<L, retaining the exact moment and positivity conditions. Empty prime index sets are included. No probabilistic independence assumption is imported: all identities are explicit finite sums/products.

ActualChebyshevLogMoment318 constructs finite Abel summation with its exact terminal term, proves the needed harmonic/log telescoping inequality from Real.log_le_sub_one_of_pos, and applies the pinned Mathlib Chebyshev theorem to the ACTUAL prime log indicator. The resulting bound for every finite actual prime subset S with p<=N is
 sum_{p in S} log(p)/p <=log4*(1+log N), N>=1.
The prefix is proved equal to Chebyshev.theta(N), not an unrelated prime distribution predicate. Primary source: Mathlib56a005855ea17e0b0958f73ec801ae140b0a1679, Mathlib/NumberTheory/Chebyshev.lean, theta_le_log4_mul_x and theta_eq_sum_Icc. Its proof derives the elementary Chebyshev bound from the primorial bound. Fintype.prod_sum is pinned in Mathlib/Algebra/BigOperators/Ring/Finset.lean. Both primary files are included for review. No Mertens theorem is assumed.

ActualSievePrimeMoment318 uses EXACTLY the existing original density nu and actual selected cutoff primes, then removes an arbitrary named prime. From the already constructed finite-field density error it proves
 0<g(p)<=1/2 and g(p)<=(5k+6)/p
on the actual retained primes, wherek is the full original coefficient count. The exact finite log moment is consequently bounded uniformly in the removed prime by
 momentBound(k,N)=(5k+6)*log4*(1+log N).
No coefficient index or exceptional-prime condition is dropped; the original predicates require the distinct coefficient family containing0 and-kappa, with kappa nonzero.

ActualTruncatedSelbergEuler318 constructs the actual natural number d as the product of the chosen retained primes. It proves d>0, d divides the actual retained prime product, and that membership of each prime is equivalent to its selected Boolean bit. Therefore the map from choices to actual integer divisors is injective; no duplicate modulus can inflate the truncated mass. The cost is proved to be log of this SAME d.

The module defines the actual Euler product E=prod_p(1-g(p))^-1 and raw odds weight prod_{p selected}g(p)/(1-g(p)). Multiplying the explicit Bernoulli probability by E gives precisely that raw weight. Thus the strict integer truncation d<z equals E times the strict cost<logz probability. It constructs
 logThreshold=1+2*momentBound(k,N), threshold=exp(logThreshold)
and proves at least E/2 lies on the distinct ACTUAL integer divisors d<threshold. All moment and cutoff inequalities are supplied internally, uniformly in the removed prime. The same threshold has the explicit polynomial expression
 exp(1+2*(5k+6)*log4)*N^(2*(5k+6)*log4).
The statement therefore gives an actual polynomial-scale truncation, not a free parameter chosen after seeing individual divisors.

Manuscript application locator: quartic_v10.tex lines16655-16689, normalized Euler weights, expected log divisor, Markov truncation and removal of one prime in the medium-prime Selberg argument. This packet constructs the elementary log-moment/strict-truncation part on the actual original finite prime set. The exact identification with the standard arithmetic-function selbergTerms denominator, the bounded factor comparison to the unremoved Euler product, the Mertens lower growth of that product, the optimal Lambda weights, and the original primitive integer-point congruence remainder remain separate next joins. No (log z)^k denominator lower bound, medium-prime count, Gaussian ray main term, or prime-pattern existence is inferred from this packet.

Validation:28 exact finite total identities,28 exact first moments,112 Markov truncations including empty and boundary cases,237 rational Abel identities,410 Chebyshev log-moment/subset checks,981 actual local density bounds,16 actual original prime moments,432 distinct modulus/integer-divisor checks,432 exact odds/probability identities,32 half-Euler truncations,16 polynomial cutoff identities. 90digits for logarithmic comparisons. Canonical438/222. No local Lean; these source/exact checks are not hosted proof acceptance.

## Independent-review parser hardening
The independent reviewer caught two unescaped Lean command keywords used as declaration identifiers. Exact whole-token renames: ActualChebyshevLogMoment318.prefix becomes partialMass; ActualTruncatedSelbergEuler318.local becomes retainedDensity. All occurrences in the corresponding modules are renamed, with no statement, formula, hypothesis or proof strategy changed. The other436 sources are exact. This is source-level parser hardening, not a claimed hosted diagnostic.
