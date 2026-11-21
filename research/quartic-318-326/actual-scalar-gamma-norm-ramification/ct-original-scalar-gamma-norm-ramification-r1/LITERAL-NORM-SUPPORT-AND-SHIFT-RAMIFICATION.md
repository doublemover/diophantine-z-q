# The literal Γ norm: a positive certificate and an exact recurrence shortcut obstruction

Fix the original scalar \(h,J,R,\beta\), with \(\beta=204618888056724185\),
\(i=6^{15}3^{65536}J\), and the actual source point \(P_0=(1+\sqrt2,2\sqrt2)\) on
\(E:y^2=x(x^2-(3-\sqrt2)^2)\). Use
\[
 D_0=1+114444R,\ H_0=N_{\mathbf Q(\sqrt2)/\mathbf Q}U([h]P_0),\quad
 N_0=1+(H_0/R)^2+\operatorname{Tr}(U([h]P_0)^2)/R,\qquad
 U(P)=2y(P)/(x(P)^2+(3-\sqrt2)^2).
\]
Here \(N_0\) is the packed scalar coefficient, not the orbit exponent 65536. At the literal input,
\(q=N_{\mathbf Q(\sqrt2)/\mathbf Q}U([i]P_0)/(H_0R^{15})\),
\(c=12(N_0^2+Rq^2)/D_0\), and \(\delta=1-\beta c^2>0\).
This note does not decide whether the **actual** \(\delta\) is a norm from \(\mathbf Q(\sqrt5)\), or whether Γ has a rational point.

## 1. The primitive original binomial in a fixed unramified quadratic layer

Write the true reduced \(c=C/D\) with \(D>0\), and \(S=D^2-\beta C^2>0\). The literal local guards give \(\gcd(S,10\beta)=1\). For instance \(c\) is integral at each \(p\mid\beta\) from \(v_p(\beta c^2)>0\), and it has positive 2-adic depth. At any rational \(p\mid S\), both \(C,D\) are units and \(\beta\equiv(D/C)^2\bmod p\). Thus \(p\) splits in \(F=\mathbf Q(\sqrt\beta)\). Among the two primes over \(p\), exactly one contains
\[
                         A_\beta=D-C\sqrt\beta ,
\]
and its order is \(v_p(S)\), because its conjugate is a unit on that arm. Both real conjugates of \(A_\beta\) are positive.

The quadratic extension \(F(\sqrt5)/F\) is unramified at finite places. Away from 2 and 5 the rational \(\sqrt5\) layer is split or unramified, and the same holds after base change to \(F\). At 2, \(F\) splits because \(\beta\equiv1\bmod8\), and the polynomial of \((1+\sqrt5)/2\) is irreducible separable mod 2. At 5 write \(\sqrt5=\sqrt\beta/\sqrt{\beta/5}\); the base is ramified with residue \(\mathbf F_5\), and the unit \(\beta/5\equiv2\bmod5\) gives the unramified quadratic extension. Both archimedean places split.

Local norms in an unramified quadratic local field are exactly the even-order elements, with no constraint on units. Hasse–Minkowski for the quadratic norm conic then proves the exact equivalences
\[
 \delta\in N_{\mathbf Q(\sqrt5)/\mathbf Q}\mathbf Q(\sqrt5)^\times
 \quad\Longleftrightarrow\quad
 A_\beta\in N_{F(\sqrt5)/F}F(\sqrt5)^\times
 \quad\Longleftrightarrow\quad
 v_p(S)\text{ is even at every }p\text{ with }(5/p)=-1 .
\]
The rational layer has no obstruction at the ramified 5-place because \(\delta\) is a square unit there. Thus this relative formulation retains one concrete principal ideal from the source rather than an arbitrary choice of oriented \(\sqrt\beta\) norm. It does not assume the class group of \(F\) is trivial.

One *aggregate* condition is automatic, without any support factorization: \((5/S)=(S/5)=+1\), since \(S\equiv D^2\bmod5\). Equivalently, nonsplit primes with odd depth must occur in an even number. This neither proves their absence nor detects two such primes. Merely computing the norm or Artin character of the entire principal ideal in this unramified layer encounters the same cancellation.

## 2. A verified positive certificate without a complete support factorization

The exact missing positive input may be given as three integers \(A,b,r\) satisfying
\[
                 S=A b^2,\qquad r^2\equiv5\pmod A,\qquad A,b>0 .
\]
\(A\) need not be squarefree. A certificate exists iff the previous norm criterion holds: even powers of inert primes can be put into \(b^2\), and all remaining split prime powers admit a square root of 5. The reverse is immediate from the odd support. Since \(A\mid S\), its coprimality to 10 and \(\beta C D\) already holds. In particular \(D/C\bmod A\) supplies a square root of \(\beta\) for free, so the root input can equivalently be a single square root of \(\beta/5\bmod A\). This last square root does not follow from the first.

Given the displayed certificate, let \(\omega=(1+\sqrt5)/2\), \(w=(1+r)/2\bmod A\). The evaluation ideal \((A,\omega-w)\) in the norm-Euclidean ring \(\mathbf Z[\omega]\) has quotient \(\mathbf Z/A\mathbf Z\) and norm \(A\), since \(w^2-w-1\equiv0\). Its Euclidean gcd generator \(\pi\) therefore has norm \(\pm A\); multiply by the norm \(-1\) unit \(\omega\) if needed. Now
\[
                         \zeta=(b/D)\pi,\qquad N(\zeta)=\delta
\]
is an explicit norm certificate for the [same Γ receiver](../ct-original-scalar-gamma-norm-certificate-r1/GAMMA-FACTORISATION-FREE-NORM-RECEIVER.md). No prime factorization or primality certificate for \(A\) is needed to verify these implications. The actual visible product \(35589230039008870789\) has verified root \(17375152611552396213\); it is only a **partial** modulus. The unrepresented complementary part of the literal \(S\), modulo rational squares, remains the gap.

## 3. No uniform norm identity on the full literal shifted chart

Hold fixed the actual \(h,P_0,R,H_0,N_0,D_0\), but let the shifted point vary on \(X=\operatorname{Res}_{\mathbf Q(\sqrt2)/\mathbf Q}E\). One may first multiply this variable point by any fixed nonzero integer, including the enormous original \(i\). This preserves all constants from the actual unshifted chart, and replaces only the original fixed shifted input. Over \(F=\mathbf Q(\sqrt\beta)\), a root \(q_*\) of the literal \(\delta(q)\) satisfies, with a choice of the \(\sqrt\beta\) sign,
\[
                     q_*^2=(D_0/(12\sqrt\beta)-N_0^2)/R .
\]
Its right side is nonzero and irrational, and at the other real embedding of \(F\) it is negative. Therefore the degree-four root field \(L=F(q_*)=\mathbf Q(q_*)\) has a complex embedding. It cannot contain \(\sqrt5\), or it would equal the totally real \(F(\sqrt5)\). The roots are simple because \(q_*\ne0\) and \(N_0^2+Rq_*^2\ne0\).

The actual identity \(U(P)^2=1/x([2]P)\) gives the *full* branch set of each source arm \(U_\pm\): the degree-two map \(x:E_\pm\to\mathbf P^1\) branches at \(0,\infty,\pm d_\pm\), \(d_\pm=3\mp\sqrt2\). Pullback by étale \([2]\) and then cancellation by the square \(U^2\) leaves \(0,\infty\) unramified for \(U\), and \(U\) branches at precisely \(\mu_4/\sqrt{d_\pm}\). Composing with any fixed nonzero multiplication does not change the branch values. Over an algebraic closure the fibre
\[
              U_+(\cdot)U_-(\cdot)=H_0R^{15}q_*
\]
is, on its nonzero finite chart, the fibre product of \(U_+\) and \(H_0R^{15}q_*/U_-\) over \(\mathbf P^1\). Their branch sets are disjoint: intersection would mean \((H_0R^{15}q_*)^2=\pm1/7\), since \(d_+d_-=7\), contrary to irrationality. Their geometric Galois closures have disjoint branch sets and trivial intersection (a common extension would be everywhere unramified over \(\mathbf P^1\)); hence the fibre is smooth and geometrically integral. Equivalently one may take its closure in a resolved product chart; base points do not affect its generic divisor.

The associated prime divisor on \(X\) has residue regular over its root field \(L\), so \(5\) is nonsquare in its residue, and \(\delta(q)\) has order one there. It cannot be a norm from adjoining \(\sqrt5\): the extension is unramified quadratic at that divisor and local norm orders are even. In quaternion terminology \((5,\delta(q))\) has nonzero tame residue. This only proves that a norm formula **uniform in the full shifted point**, even after its literal fixed multiplication, cannot work. It does not specialize this obstruction to \(P_0\).

## 4. Small exact local counterexample to using the multiplication image alone

At \(p=2887\) the true source splits into two arms (2 square), \(\beta\) is square, and 5 is nonsquare. Hold fixed the same actual unshifted \([h]P_0\) coefficient data \(H_0=753,\ N_0=141\bmod p\), and use the **same exact** shift multiplier \(i\). Both source arm groups have order 2888 and \(i\equiv1480\bmod2888\). The following different local inputs in those arms have true images:
\[
 \begin{array}{c|c|c}
  Q\bmod p &[i]Q\bmod p&U([i]Q)\bmod p\\ \hline
  (2805,2480)&(497,1059)&1491\\
  (2181,204)&(1882,1309)&1987 .
 \end{array}
\]
Thus \(q=1295\bmod p,\ \delta(q)=0\bmod p\). These same base abscissas have lifts with ordinates \(1171715,4062213\bmod p^2\) in the chosen two arms. Exact calculation of the unshifted \(U_h^2\) and these shifted \(U_i^2\) modulo \(p^2\) gives \(\delta(q)\equiv136p\bmod p^2\). This is an actual local nonnorm for a point in the image of **that** multiplier, not only a root on an abstract finite fibre. The true original shifted point \([i]P_0\) instead gives \(\delta\equiv1634\bmod p\), so it is not a literal obstruction.

The second-order replay uses the short Kummer \(x\)-ladder, the square identity for \(U^2\), and \(p\,\#E(\mathbf F_p)\) as an annihilator mod \(p^2\) (the good-reduction first formal kernel has exponent \(p\)). Its adjacent inputs have differential difference the literal base point, which is neither \(O\) nor \((0,0)\); no simultaneous numerator/denominator zero occurs. The Euclidean norm receiver replay contains an exact non-Ready fixture with a square factor in two possible allocations. Neither replay establishes the required complementary certificate, an actual odd-depth inert prime, a Γ point, or any rank.
