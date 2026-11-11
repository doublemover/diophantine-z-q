# Coprime multiplicativity of the actual unit-frequency coefficient

This packet proves the missing unit-frequency CRT bridge. It does not infer it from the earlier complete-average count CRT.

At coprime moduli m,n, the frequency merge sends (a,b) to n*a.val+m*b.val modulo m*n. Its bijection is constructed as multiplication by the actual units n mod m and m mod n, followed by inverse ring CRT. The component and literal representative formulas are proved. The resulting map restricts to a bijection from the product of the EXACT IsUnit subtypes to the IsUnit subtype at m*n. This cross-scaling is necessary: unscaled residue CRT does not directly split the standard additive characters.

The actual residue CRT is separately the ordinary coordinatewise ring CRT followed by regrouping all five original coordinates. Standard-character compatibility is proved directly from exp(2*pi*i*a/q), with the divisor modulus and quotient multiplier explicit. Applied to the frequency-merge formula and the same original quadratic equation, it gives the exact product of the two standard phases. Finite summation is then reindexed through the full original residue equivalence and the full unit-frequency equivalence. Product sums and the explicit (mn)^5=m^5*n^5 normalization prove actual unitAverage(kappa,m*n)=unitAverage(kappa,m)*unitAverage(kappa,n).

The statement covers arbitrary coprime nonzero moduli, not only distinct primes or squarefree numbers. Modulus1, prime powers and exceptional primes are included. The original integer kappa is retained through both coefficient maps. No primitive-point scaling is introduced.

Remaining global-series obligations: absolute summability over all positive denominators and justified equality between that global sum and the already established full positive local Euler product. Coprime multiplicativity and absolute local series alone are not asserted to imply global convergence. Poisson inversion, uniform arc estimates and the global count also remain separate.

All578 predecessor sources unchanged; three new modules. Six pinned primary API copies cover ring CRT, actual units and multiplication equivalences, standard characters and finite sums. Exact24 regressions test unit domain bijections, all phase exponents, the full original five-coordinate residue distributions and rational unit coefficients for both forms, including coprime powers and modulus1. No local Lean or profiling; source and finite checks are not kernel acceptance.
