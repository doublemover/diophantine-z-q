# Exact crossed Cassels characters without expanding the translated point

Keep the unchanged \(a=0\) scalar and literal \(h,i=mh\), \(R,\beta\), \(K=1+2448\beta\). This concerns only the two still-unknown **exceptional denominator** characters in the [positive zero-ordinate row](../actual-zero-ordinate-aggregate-norm-admission-r2/), not the separate rational conic norms for actual admission of its test classes. It reduces the signed computation to one \(h\)-side integer and modular operations. It does not compute that integer or either sign for the original scalar.

## 1. Exact raw numerators and which valuations matter

Use the primitive good-place division chart from [Joined's division recurrence](../../../joined-work-20261120/rc-linked-scalar-division-normalizer-r1/EXACT-DIVISION-SLP-AND-NORMALIZER-CERTIFICATE.md). Write \(U_j=a_j/b_j\) there, reserve \(\mathrm N\) for the norm from \(\mathbf Q(\sqrt2)\), and set
\[
 U=\mathrm N b_h,\quad V=\mathrm N b_i,\quad
 S_h=\mathrm N a_h,\quad S_i=\mathrm N a_i,\quad
 P_0=\mathrm N(Rb_h^2+a_h^2).
\]
The exact unreduced scalar is
\[
 c=\frac{12F}{K R^{29} U^4 V^2 S_h^2},\qquad
 F=R^{25}P_0^2V^2S_h^2+U^6S_i^2 .
\]
No modular inversion or chart cancellation is used to produce these polynomial numerators. Repeated use of the prior good-place chart primitivity and formulae is legitimate over any modulus away from the fixed bad support.

Let the excluded prime support consist of the bad curve/chart places \(2,7\), the normalizing support \(3 R K\beta\), all primes dividing \(m\), and the two **fixed character conductors** \(s_1=2952271997968816765,\ s_2=5566083893370034\). The factors of all of these integers are fixed and known; the actual extra \(3\)-power in \(m\) adds no extra prime. No genuine exceptional odd denominator prime is excluded by the additional fixed \(m,s_1,s_2\) guards: all their primes are smaller than the previously checked [same-scalar exceptional support bound](../../../joined-work-20261120/rc-linked-scalar-norm-pair-denominator-grid-r1/). Its four known normalizer denominator primes are not included in \(D_{\mathrm{exc}}\); their contribution to the two Cassels signs remains the already known factor. Denote any positive fixed gcd-removal integer with this support by \(M_{\rm fix}\).

An extra odd pole of \(c\) requires a pole of \(U_h\) on one arm and a pole of \(U_i\) on the other, with the other \(h\)-chart a unit. Indeed at a prime where \(U_h\) is integral on both arms, the \(N^2\) term is integral, so no negative odd cancellation with \(RQ^2\) is possible. At a good place chart numerator and denominator are primitive, multiplying a pole (order four whose double is \((0,0)\)) by the even integer \(m\) destroys it, and a chart zero (at a two-torsion reduction) goes to another zero with integral ratio. This excludes a lone inert arm, two \(h\)-poles, and an opposite \(h\)-zero. Equivalently all extra odd primes survive in the part \(B_0\) of \(|U|\) coprime to \(S_h M_{\rm fix}\). At each of its primes write
\[
 a=v_p(U)>0,\qquad b=v_p(V)\ge0,\qquad u=v_p(P_0)\ge0 .
\]
If \(b=0\), the second raw numerator term has valuation at least \(6a>4a\), so there is no odd denominator. If \(b>0\), primitivity and the even shift force exactly the two opposite poles and the two other charts as above. On the \(h\)-pole arm the chart pole has depth \(a\). Translating the doubled point away from \((0,0)\) makes the formal parameter also have depth \(a\), by \(U_h^2=1/x([2h]P)\) and the order-two zero of \(x\) at this point. The shift \([m]\) has unit derivative at these primes and removes the torsion component, giving \(U_i\) a zero of depth \(a\) on that arm. On the opposite \(i\)-pole arm, \(a_i\) is a unit. Hence
\[
                        v_p(S_i)=a .
\]
So the raw numerator term depths are \(2(u+b)\) and \(8a\), and the denominator depth is \(4a+2b\). Odd negative depth is possible only at a tie \(u+b=4a\) **and** \(b>2a\), since otherwise equal summands are already at least as deep as the denominator. This recovers the known crossing test without requiring any prime-factor roster for \(U,V\).

## 2. A one-step modulus or a staged smaller one

All following support exclusions are factor-free. For any positive \(B\), its whole prime-power part supported on the primes of an integer \(J\) is \(\gcd(B,J^{\mathrm{bitlen}(B)})\), evaluated by modular powering (if \(J=0\), the whole part is \(B\)). Its complement is an exact quotient. This is how \(B_0\) is extracted from the materialized \(|U|\), using \(S_h\) only modulo \(|U|\).

**Single modulus.** Evaluate \(V,S_i,P_0,S_h\) modulo \(B_0^{12}\) using the fixed-window modular division recurrence, and put
\[
     L_0=B_0^4\gcd(V,B_0^4)^2,\qquad A_0=L_0/\gcd(F,L_0).
\]
Then \(A_0\) has the same odd-valuation support as \(D_{\rm exc}\). For \(b\le4a\), \(L_0\) has the exact raw local denominator depth and divides \(B_0^{12}\), so its gcd with \(F\) makes the exact local reduction. For \(b>4a\), the first term has valuation \(>8a\) and the second exactly \(8a\); the truncated denominator has depth \(12a\). The residual exponent \(4a\) is even, which agrees with the true even residual exponent \(4a+2b-8a\). Thus clamping does not alter the character. If \(B_0=1\), there is no exceptional contribution.

**Staged receiver.** First evaluate \(V\) modulo \(B_0^3\); retain in \(B_1\) precisely the whole prime powers of \(B_0\) supported on
\[
        \gcd(V,B_0^3)/\gcd(V,B_0^2).
\]
This is exactly the strict test \(b>2a\). Next compute modulo \(B_1^5\) and set \(G_2=\gcd(P_0V,B_1^5)\) and \(J_2=\gcd(G_2,B_1^4)\). Remove from \(B_1\) the whole prime powers supported on
\[
                          (B_1^4/J_2)(G_2/J_2).
\]
The first quotient detects \(u+b<4a\), and the second \(u+b>4a\) even at the overclamp \(5a\). Let \(B\) be the remaining integer. All its primes satisfy the exact tie and \(2a<b\le4a\); all others are known to contribute no odd phase.

On \(B\), divide the two summands by the common even power \(B^8\), and use
\[
\begin{split}
 G&=R^{25}\bigl(P_0V/B^4\bigr)^2 S_h^2+(U/B)^6(S_i/B)^2,\\
 L&=\left(\frac{\gcd(V,B^4)}{B^2}\right)^2,\qquad
 A=L/\gcd(G,L).
\end{split}
\]
All indicated divisions are exact over the integers on this surviving modulus. The raw denominator remaining after division has depth \(2b-4a\), exactly the depth of \(L\), and \(L\mid B^4\). To obtain \(G\bmod B^4\), compute \(P_0V\bmod B^8\) and \(S_i\bmod B^5\) **before** their divisions; this is exact modular division by known divisors, never inversion of a nonunit. \(U/B\) is also an exact quotient. For any empty stage set \(A=1\). By construction on every selected prime \(p\), \(v_p(A)\) equals the actual positive reduced denominator depth if there is one, and is zero otherwise. Every omitted prime would have contributed an even depth or none. Therefore
\[
  \left(\frac{s_j}{D_{\rm exc}}\right)=
  \left(\frac{s_j}{A}\right)=
  \left(\frac{s_j}{A_0}\right)\qquad (j=1,2).
\]
All three denominators in these symbols are odd and coprime to the fixed test entries. This identifies the signs by gcd and Jacobi arithmetic with no factorization of either large chart norm and no hidden-prime count requirement.

## 3. What is and is not efficient here

The largest translated computation can now remain modular, in stages \(B_0^3,B_1^5,B^8\) instead of ever expanding the \(104414\)-bit-index point \([i]P\). The fixed-window recurrence takes \(O(\log i)\) ring operations in each such modulus, with the result checks only gcd, exact divisions and Jacobi symbols. A single-modulus version needs only \(B_0^{12}\). This is a genuine reduction to the \(h\)-side norm; it is not a practicable computation for the given \(h\). Materializing \(\mathrm N(b_h)\), or supplying a smaller certified equivalent modulus \(B_0\), remains unresolved. Its raw bitlength grows on the \(h^2\) scale for a fixed non-torsion source point, and the size after support removal is not known on the literal input. No claim about computational lower bounds is made.

The standard-Python replay uses artificial integer tuples satisfying the local depth templates. It compares both receivers to an independent exact reduced rational denominator and exercises strict-boundary, under-tie, over-tie, \(S_h\)-deletion, vanishing after exact division, and both character signs. These are signed arithmetic controls, not additional found primes or results for the actual translated source. The package supplies **neither** actual exceptional phases **nor** the separately required pair of positive admission norms or any rational point.

    python3 -B check_crossed_sign_modulus.py | cmp - EXACT-CROSSED-MODULUS-CONTROLS.json
