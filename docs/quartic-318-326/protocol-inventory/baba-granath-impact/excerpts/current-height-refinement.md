<a id="finite-exceptional-primes"></a>

## Finite exceptional-prime refinement for the 318-coordinate source

### Proposed fixed set

Let

    S_bad = {2,3,5,7,11,13,17,37,41,73,109,359,439,2399,4801}.

Every listed number is prime. Their product is

    B_bad = 11185621387570686764517810 < 2^84.

Define M5(a) using exactly the inherited five contacts infinity, 0, 1, 2401, -343/32, but omit only S_bad. The associated detector radicals use the five positions 0,-1/2,-1,1/2399,-32/407, again omitting S_bad.

This change does not change any polynomial row. It is a stronger soundness argument about more primes. Completeness can retain its old choice of primes greater than 76176 and every old local congruence; no stronger prime-pattern theorem is needed.

### Consumers of exceptional primes

1. **Five-contact geometry and height theorem.** The inherited moduli argument is smooth outside210, and every determinant of the primitive five contact forms has support in{2,3,5,7}. The exact same ramification statement therefore holds with R=B_bad*M5(a): rad(D_L*N_bad) divides R. See quartic_v10.tex lines6915--7001. None of the modular-support, direct-finite-divisor, metric-cancellation or fixed-dimensional isogeny arguments needs a lower bound76176 on the primes of R. They use only its prime support and size. Thus the reviewed49/8 theorem applies with this new B_bad.

2. **Detector contact map and its delta denominator.** The five positions together with 1 have all numerator, denominator and pairwise-difference support in{2,3,5,7,11,37,109,439,2399}. This is also the exact list printed in the inherited height-transfer proof (lines11108--11117). Outside that list, consumed contacts have delta=t-1 a unit and exactly one odd factor. The map phi(t)=2+1/t has determinant-1. The degenerate t=1 branch has phi(1)=3 and every contact prime lies in this same set, so its new radical is still1.

3. **Elliptic model, fixed translation and orientation.** K/Q is unramified away2. D=(3-sqrt2)^2 has norm49, so good unramified local computations require only2,7. The fixed P has x=(57-28sqrt2)/8 and y=(-660+417sqrt2)/32. The numerator norms factor as41^2 and 2*3^2*7*17*41. Hence x(P),y(P) are units at both places outside{2,3,7,17,41}. This covers the Norm(V0) orientation contradiction and the exceptional H=P branch. The h(P),j(P) constants have numerator norms -2*41 and -3^2*7*17, adding no primes. Other group identities are characteristic-zero identities and use no prime cutoff.

4. **Pole soundness.** The exact original and preparation-zero pole lemmas exclude negative odd valuations at every prime outside{2,3,17}, not merely above76176. Normalized pole equivalence introduces no prime restriction. The norm-chain parity argument needs only odd residue characteristic, unramifiedness and D a unit. The new affine delta=v-1 leaves have even valuation for every such prime, as proved in [the derivation](#parity-even-linear-delta-leaves).

5. **Scalar input and contact collisions.** beta=3723(2X+1)^2, with 3723=3*17*73. Outside{2,3,17,73}, any nonzero valuation of beta is even, so the omitted beta=0 and infinity contacts cannot be odd. The four retained factors are(beta-1),(beta-2401),(32beta+343),(2beta-1). All pairwise collision and denominator primes of 0,1,2401,-343/32,1/2 lie in{2,3,5,7,359,4801}; specifically718=2*359 and 4801=2*2401-1. At a consumed contact the relevant r valuation is positive odd and the other factors are units. The correction11 and normalizer114444=11*(2*3*17)^2 add only{2,3,11,17}. Global nonvanishing of r, W and 1+114444*r is the independent rational squareclass/Q2 argument, unchanged by this inventory. beta=0 continues to use h(beta)=0 directly.

6. **Actual rational logarithms and precision.** The high Padé(2,1) coefficient denominators have prime support{3,5,13}; the low J1 has denominator5. At a formal point their quotient denominators are units outside those primes. Their exact errors begin in degree 4. The full formal series has coefficients binom(2j,j)/(4^j*(4j+1)) in reciprocal u, and the rational z-series differs by the square-root factor with coefficients integral away2. The required relative precision 16 and the weak primary-log unit estimate hold for p>17 by the sharper coefficient argument below. Every prime outside S_bad is at least19. Global Padé denominator/numerator nonvanishing is already proved over K and imposes no further local exclusions.

7. **Anchor and real completeness.** The fixed anchor is tested only at 2,3; its half-norm and parity proof is unchanged. Real selection and preparation-zero completeness are unchanged. The selected Gaussian primes can still be chosen above76176, so their reduction-order, ray and quartic-reciprocity lemmas need no extension to small primes.

### Independently verified tail estimate

For H_j=binom(2j,j)/(4^j*(4j+1)), at an odd prime p one has v_p(H_j)>=-v_p(4j+1). If p>17, then for every j>=4,

    4j - v_p(4j+1) >= 16.

For j=4 this follows because p does not divide17; for j>=5 it follows from v_p(4j+1)<=4j-16 (indeed logarithmic growth is much smaller). Hence at v(u)>=1, each omitted term relative to u has valuation at least16*v(u); valuations tend to infinity. The expansion in delta=v-1 has v(delta)=4v(u) on the forced positive branch, and the exact rational change of variables has denominators only2. The analogous G series is obtained by multiplying by the binomial square-root series, integral away2. Thus the same order 16 estimate applies. The complete change-of-series and actual quotient-denominator check is written in [the derivation](#small-prime-log-tail).

### Resulting proof and anchor constants

The reviewed contact theorem becomes

    h(a) < 2^68*C^2*(B_bad*M5(a))^(49/8)+128,
    C=210^300<2^2400.

The logarithm of the coefficient before+128 is below

    68+4800+(49/8)*84 = 5382.5.

Adding128 raises this by less than 1. The integer proof constant

    H_small = 2^5385

is therefore safe. It is a proof constant, not a new circuit coordinate.

