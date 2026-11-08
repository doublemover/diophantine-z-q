<a id="height-49-over-8"></a>

## Contact-height exponent 49/8 by metric cancellation

### 1. Inputs and coordinates

Use the same Q-defined modular cover X_H -> X(1), genus g>=2, degree d, level N, and pi=1728/j as in the preceding height13 and 37/4 notes. All conjugate complex covers have the same level and degree; in the actual application the cover and map are Q-defined. Choose a non-Weierstrass b above one of a_i=1/(2^128+i), 1<=i<=g^3+1. There are at most g^3-g geometric Weierstrass points, so one fiber avoids them. Every complex lift has imaginary part above10 in a cusp coordinate q_c=exp(2*pi*i*tau/m_c), with width m_c<=N.

The explicit elementary j-expansion and embedded-disc estimates in [the derivation](#cusp-coordinate-estimates) give

- h(a_i)<=100+3log(g+1);
- -log|d pi/dq_c|(b_sigma)<=h(a_i)+9;
- an embedded Euclidean q_c-disc centered at b_sigma of radius rho>=exp(-21)/N.

No Arakelov Green-function estimate is needed below. The local coordinate may vary with sigma; the two metric occurrences use exactly the same q_c at that embedding.

### 2. Direct finite-place domination

Use docs/arithmetic.md#direct-divisor-finite-bound. On the semistable minimal resolution Y' of the normalization of P1_O_L in X_H, let K_Y'=div(d pi). The modular vertical-support lemma restricts branch primes to p|6N. Set m_p=floor(logd/logp) and

    D_bound=[0]+[1]+[infinity]+2 sum_(p|6N) m_p div(p).

At nonexceptional prime divisors, Javanpeykar Lemma4.2.3 gives the exact coefficientwise inequality K_Y'<=f^*D_bound. The horizontal inequality follows from e-1<=e; the -2[infinity] base canonical divisor only helps. Vertically, the coefficient is at most2e*m_p*e_p, precisely the coefficient of the displayed pullback.

For Z=f^*D_bound-K_Y', minimality and adjunction give Z.E=-K_Y'.E<=0 at each exceptional curve. If the negative part N_Z were nonzero, it would be exceptional and N_Z.E>=Z_+.E>=0 on its components, contradicting negative definiteness. Thus Z is effective. Intersecting the chosen section, whose generic point lies outside the branch support, gives

    F_b:=(K_Y',b)_fin/[L:Q]
      <=3h(a_i)+2 sum_(p|6N) floor(logd/logp)logp
      <=3h(a_i)+2omega(6N)logd.

The point-height inequality is the minimal-model inequality in Javanpeykar Lemma2.3.1; we do not assert equality of the stable minimal height and the chosen-resolution height.

### 3. Exact metric cancellation

Let k=g(g+1)/2. Javanpeykar Theorem2.4.1 states

    h_F(J_H)<=k*h(b)+log||Wr||_Ar(b).

His definition of h(b) and the displayed decomposition in the proof of Theorem4.5.1 give

    h(b)<=F_b - avg_sigma log||d pi||_Ar(b_sigma).

At each embedding, write d pi=(d pi/dq_c)dq_c and Wr=Wr_q*(dq_c)^k. Then

    log||d pi||_Ar=log|d pi/dq_c|+log||dq_c||_Ar,
    log||Wr||_Ar=log|Wr_q|+k log||dq_c||_Ar.

Consequently the metric terms cancel exactly, preserving the inequality:

    h_F(J_H)<=k F_b
       -k avg_sigma log|d pi/dq_c|(b_sigma)
       +avg_sigma log|Wr_q|(b_sigma).

There is no remaining Bruin metric bound, cusp-width-linear metric term, or Green-function normalization constant. This is a different way to combine the two published quantities, not a claim that each quantity separately has a stronger bound.

### 4. Wronskian coefficient bound

For an L2-normalized holomorphic differential omega=f(q_c)dq_c, its integral on the embedded disc is at most1. Orthogonality of power series on the disc gives

    |f^(j)(b)/j!|<=sqrt((j+1)/pi)*rho^(-j-1).

Applying Hadamard to the g by g matrix of derivatives gives the previously verified generous estimate

    log|Wr_q|(b)<=100g^2 log(2gN).

This estimate uses only the local Euclidean disc and the global L2 normalization, not an estimate on the Arakelov cotangent metric.

Put L=log(6dN). Since g<=d, omega(6N)<=log(6N)/log2, h(a_i)<=100+3log(g+1), and L>=log6, the preceding bounds give, with ample slack,

    h_GR(J_H)<=2^11*d^2*L^2.                        (1)

Normalization: Javanpeykar Lemma2.4.4 compares the original height h_Fal with the shifted height h_shift=h_Fal+g log(sqrt(pi)). The preceding cancellation bounds h_Fal. Add g log(sqrt(pi))<g; the displayed2^11 bound absorbs this, and(1) and the later h_F budget use this larger shifted height. The linked Gaudron-Rémond Theorem1.9 uses the original height. Its maximum is bounded by the maximum using h_shift, so the larger budget is valid without identifying the two conventions. Equal-dimension isogeny variation is unchanged by the shift.

For example F_b+h(a_i)+9<=409+12log(g+1)+2log(6N)logd/log2, and the Wronskian term is at most100d^2L. All these terms are below the right side of(1).

### 5. Explicit contact exponent

Retain N<=C R^2, C=210^300 and R=B_* M5(a). The elementary index estimate may be sharpened to

    d,g<2^14 C R^(97/32).

Indeed (1+1/p)^32<=p for p>=13, and the remaining product over 2,3,5,7,11 is1152/385<3. This is the same index argument as the independently checked73/24 estimate, with the indicated elementary Euler-product exponent. Since3*4608<2^14, the prefactor is unchanged.

Now L<4096+6logR<2^13 R^(1/32), using logR<12R^(1/32). Inserting this and the index bound in(1) gives

    h_F(J_H)<2^65 C^2 R^(49/8),

because 2*(97/32)+2*(1/32)=49/8.

The actual image C_A of the source's nonzero A->J_H map has dimension2. Rémond Corollary1.2 and the existing Bost lower bound imply

    h_F(C_A)<=h_F(J_H)+3g/2<2^66 C^2 R^(49/8).

Apply Gaudron-Rémond Theorem1.9(1) directly in dimension2, with no polarization hypothesis, over L', [L':Q]<=2304R. The half-log isogeny variation is

    8*(32log14+logd'+log max(1,logd',h_F(C_A))),

which is smaller than 2^17 R^(49/8). Hence

    h_F(A)<2^67 C^2 R^(49/8),
    h(a)<2^68 C^2 R^(49/8)+128.

The inherited CM bound854R is a bound for the original surface height h_Fal(A), not directly for h(a). Combining it with the actual metric comparison h(a)<=2h_Fal(A)+120 gives h(a)<1708R+120, still smaller than the displayed contact cap. The positive log(pi) normalization shift is also absorbed by the same cap. The old constant H19=2^110 C^6 B_*^19+128 therefore remains valid for

    h(a)<=H19*M5(a)^(49/8).                         (2)

### 6. Adopted source consequence

Use low order 4, high order 13, norm-H order 4. The primary z/full-log relative precision is16. A Pade(2,1) approximation gives alternate relative precision 16 with only one field quotient helper; its numerator is quadratic and denominator affine. Low J1 already has precision 8.

The conditional five-helper weight chain is

    a=e^2,
    c*delta=a^2,
    q4*(e*delta)=c^2,
    q1*q7=q4^2,
    q1*q13=q7^2.

Thus c=e^4/delta, q4=e^7/delta^3, q7=e^13/delta^3 and q13=e^25/delta^3 on the ordinary branch. The existing t=1 exceptional-height branch handles e=0, exactly as in the frozen 332/335 sources. The quotient outputs must remain free structural witnesses, not falsely documented globally nonzero quotient gates.

The high contradiction exponent is2-4*(49/8)/13=3/26. The old 3^(2^25) anchor gives c>(80H)^12 and therefore more than the required power9. The low exponent is2-(49/8)/4=15/32. The adopted scalar uses order 15 with ri^16, preserving index 8: the full norm-ratio valuation is at least30, one local valuation is at least15 and is even after formality, so it is at least16. Then h(beta)<=H*c^(49/64), and c^(15/64)>80H follows easily from log2(c)>25,165,823.5 and log2(H)<2,093,966. The old W<2 real-completeness estimate replaces r^-61 by r^-29, still harmless for r>=10.

These mathematical consequences are used by the frozen 318-coordinate construction. A counting correction is essential: the three variable J logarithms must retain their delta-squared helpers for the branch membership tests, so replacing their Padé(3,2) approximants by Padé(2,1) does not remove those coordinates. Only V0 loses its unshared input-square helper, saving two rational coordinates. Together with three saved weight helpers and one scalar-power helper, this stage measured332->326. The subsequent parity-even linear delta refinement removed eight more coordinates, giving318. The accepted smaller fixed-anchor and ordinary-lift proofs are separate notes; the ordinary companion has326 variables.
