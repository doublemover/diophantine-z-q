# Whole chart-zero stratum by a compressed elliptic recurrence, plus exact depth at 7

This uses the unchanged literal scalar \(a=0\), \(h,J,R,\beta,A_s\) of [the materialized source](../../../joined-work-20261120/rc-linked-scalar-specialization-r1/ACTUAL-MATERIALIZED-SCALAR-SPECIALIZATION.md), not a newly selected pole or a centered replacement of \(W\).
Write
\[
 i=6^{15}3^{65536}J,\quad m=i/h\in4\mathbf Z,\quad K=1+A_s,\quad
 \lambda=1+432\beta W^2/K^2 ,
\]
where \(W=N^2+RQ^2\) and
\(N=1+(H/R)^2+2f/R,\ Q=I/(HR^{15})\).
The original \(H,I,f\) are \(H={\rm N}U_h,\ I={\rm N}U_i,\ f={\rm Re}(U_h^2)\) on the actual curve
\[
 E:y^2=x^3-(3-\sqrt2)^2x,\quad P=(1+\sqrt2,2\sqrt2),\quad
 U_n=\frac{2y([n]P)}{x([n]P)^2+(3-\sqrt2)^2}.
\]
The quotient \(I/H\) is taken in the rational function field first and then reduced. The proof below neither treats \(H=0\bmod p\) as an illegal denominator nor sets that quotient arbitrarily.

## 1. Exact condition when both \(h\)-charts vanish

Let \(p\nmid 2\cdot3\cdot7\cdot R\beta K\). Work in the two split completions of \(\mathbf Q(\sqrt2)\), or its single unramified quadratic completion in the inert case. If \(U_h\) reduces to zero in **both split arms**, or in the single inert arm, \([h]P\) lies in the residue 2-torsion including \(O\) in each arm. Indeed the chart has a simple zero at \(O\) and each finite 2-point, and no cancellation at a zero of the denominator: there \(x^2=-(3-\sqrt2)^2\), hence \(y\ne0\) at good odd \(p\). This condition is exactly that \([2h]P\) is formal simultaneously in the corresponding arms.

Since \(m\) is even, \([i]P=[m][h]P\) is formal in those arms. On translating a finite residue 2-point to \(O\), the quotient of the local leading coefficients of the chart is \(+1\) or \(-1\), so at each arm
\[
                 U_i/U_h\equiv\pm m\pmod p .
\]
For detail, with \(t=-x/y\) at \(O\), \(U=-2t+O(t^5)\) and the invariant differential starts \(dt\). At a finite 2-root \(e\), the coefficient \(dU/\omega\) for \(\omega=dx/(2y)\) is \(2(3e^2-(3-\sqrt2)^2)/(e^2+(3-\sqrt2)^2)\). This is \(-2\) at \(T_0\) and \(+2\) at the other two roots. Multiplication by \(m\) on the translated formal disk has derivative \(m\), giving the quotient also when \(p\mid m\). Norm and the final square remove the signs. As also \(H\equiv f\equiv0\), we get
\[
 \quad W\equiv 1+\frac{m^4}{R^{29}},\qquad
 \lambda\equiv0\ \Longrightarrow\
 p\mid M:=K^2R^{58}+432\beta(R^{29}+m^4)^2.
\]
The integer \(m\) has 104335 bits and \(M\) 834742 bits. Strip all powers of the known fixed bad support via repeated gcd with \(2\cdot3\cdot7\cdot R\beta K\); the remaining composite \(M_{\rm good}\) has 831729 bits. No factorization of it or enumeration of primes occurs.

## 2. Complete rational x-ladder over the unexpanded-support modulus

Use x-coordinates \((X:Z)\) on \(y^2=x^3+a_E x\), \(a_E=-(3-\sqrt2)^2\). The exact doubling and fixed-difference sum are
\[
 \operatorname{dbl}(X:Z)=((X^2-a_EZ^2)^2:4XZ(X^2+a_E Z^2)),
\]
\[
 \operatorname{add}_{P}((X:Z),(X':Z'))
 =((XX'-a_EZZ')^2:(XZ'-X'Z)^2 x(P)).
\]
The second identity is the usual \(x(A+B)x(A-B)=(x(A)x(B)-a_E)^2/(x(A)-x(B))^2\), by the two slope formulas. It is used only for adjacent multiples with difference \(P\), in the binary ladder from \((O,P)\). Doubling has no projective base point in any good odd characteristic: if its first coordinate vanishes then \(X^2=a_E Z^2\), both \(X,Z\) are nonzero, and \(X^2+a_E Z^2\ne0\). For fixed-difference addition, simultaneous vanishing could only occur if the two x-coordinates were equal; adjacency then implies the points are negatives (they cannot be equal). If they are finite with \(x^2=a_E\), their double is the finite 2-point \(T_0\), forcing difference \(P=T_0\), impossible since \(x(P)=1+\sqrt2\) is a norm-\((-1)\) unit. They cannot be both infinite since \(P\ne O\). Thus induction proves these exact polynomial operations recover eligible projective coordinates at every residual arm on the composite modulus.

If \(Z([2h]P)=z_0+z_1\sqrt2\bmod M_{\rm good}\), both split arms vanish (or the one inert arm does) exactly when \(p\mid z_0,z_1\). The exact GMP replay gives
\[
             \gcd(M_{\rm good},z_0,z_1)=1.
\]
It even gives \(\gcd(M_{\rm good},z_0^2-2z_1^2)=1\) for this particular necessary candidate modulus, and the analogous results for \([h]P\). **The λ implication uses simultaneous chart zeros; the norm-gcd statement alone cannot test λ on a singly zero or generic regular arm.** This rules out the whole specified \(h\)-chart-zero stratum, not all odd factors of \(\lambda\).

## 3. The excluded prime 7 is not an odd-support prime

The bad arm over 7 is \(\sqrt2\equiv3\), with additive cuspidal reduction for the displayed minimal equation (discriminant depth 6). The point \(P\) is in the smooth subgroup of the reduction, whose size is 7; its smooth reduction modulo \(7^k\) has exponent dividing \(7^k\) since each further formal grade has order 7. The same x-ladder on an adjacent pair of smooth points is complete mod 7 on this cusp as well: every smooth finite point has \(x\ne0\), and the first sum coordinate in the formula with \(a_E=0\) is nonzero even at \(O\). For \(h,i\) units mod 7 recover the affine x-coordinate and use the known additive-residue y-sign followed by Hensel. Modulo \(49\), the arm's coefficient \(a_E\) is zero, so one can also compute the exact additive chart directly there.

The arm \(\sqrt2\equiv4\) has good reduction and \(P\bmod7\) has exact order 4. Evaluate the small rational-field point \([4]P\) exactly, with \(v_7(t([4]P))=1\). On this arm the formal logarithm is explicitly
\[
 \log_E(t)=\sum_{j\ge0}\frac{(-1)^j\binom{2j}{j}D^j}{4j+1}t^{4j+1},
 \qquad D=(3-\sqrt2)^2 .
\]
Indeed \(\zeta=t^2x=(1+\sqrt{1+4Dt^4})/2\) and \(dx/(2y)=dt/(2\zeta-1)\). Apply the exact multipliers \(h/4,i/4\) in this log and invert it by successive 7-adic digits, then use \(U=-2t\zeta/(\zeta+2Dt^4)\). Both original charts have valuation 1 on this arm, so use one extra digit before taking \(U_i/U_h\). The sums are genuinely finite modulo any archived power: subsequent terms have valuation at least \(4j+1-v_7(4j+1)\). This calculation recovers the previously frozen \(W\equiv5,c\equiv1,\mu\equiv2\bmod7\), and then the exact values
\[
 (\lambda\bmod 49)=0,\qquad (\lambda\bmod 343)=147 .
\]
Consequently \(v_7(\lambda)=2\) and the stripped unit is \(3\bmod7\). In particular 7, although a true zero of the unstripped numerator and \((3/7)=-1\), does **not** contribute to the marked Cassels odd-support row.

The exact checkpoints do not provide a nontrivial split of \([\lambda]\) or a rational point. Their only roles are a factor-free no-factor whole-stratum statement and one precise formerly exceptional local depth. No remote or Lean use.

    c++ -O3 -std=c++17 check_formal_lambda_gcd.cpp -lgmpxx -lgmp -o /tmp/check_formal_lambda_gcd
    /tmp/check_formal_lambda_gcd | cmp - EXACT-FORMAL-LAMBDA-GCD.txt
    python3 -B check_actual_lambda_at_seven.py | cmp - EXACT-ACTUAL-LAMBDA-SEVEN.json
