# The same marked Γ as a sparse binary quartic

This is an exact constructive receiver for one *particular* multisection of the original scalar Kummer, with one certified bounded exclusion. It does not exclude Γ at larger height or other points of the original Kummer. No hidden θ prime is assumed or found. Keep the [literal original scalar and the marked Γ](../ct-original-scalar-mestre-marked-genus-one-r1/LITERAL-MESTRE-MARKED-MULTISECTION.md), with \(\beta=204618888056724185\), the exact compact \(c\), \(\delta=1-\beta c^2>0\), and \(\theta\) its positive squarefree class. The two Γ equations were \(5B^2=u^2+1/\delta\) and \(5A^2=\beta(u^2-4/\delta)\).

## Exact sparse form with fixed binary coefficients

Put \(H=\delta B,\ K=\delta A/\beta,\ Z=\delta u\). These equations become
\[
H^2-\beta K^2=\delta,\qquad Z^2=4H^2+\beta K^2.
\]
All \(H,K,Z\) are nonzero at any rational point of the old Γ. For example \(K=0\) would make \(\delta\) a square, and \(H=0\) or \(Z=0\) is excluded by the original real inequalities. Hence \(Z+2H\ne0\). The second equation is a rational conic in \(K/H,Z/H\), independent of \(\delta\). Its parametrization \(r=K/(Z+2H),\,s=(1-\beta r^2)/H\) gives the equivalent equation
\[
F(r)=1-18\beta r^2+\beta^2r^4=\delta s^2 .                    \tag{1}
\]
Its inverse is \(H=(1-\beta r^2)/s,\ K=4r/s,\ Z=2(1+\beta r^2)/s\). Denominators cannot vanish: \(\beta\) is nonsquare, \(F\) has no rational zero (the two roots in \(\beta r^2\) are \(9\pm4\sqrt5\)), and the quartic cannot have \(r=0\) or a rational infinity because \(\delta\) is nonsquare. There is no separate requirement to furnish a \(\sqrt5\)-norm, a rank bound, or integer coefficients of the original fold. One solution of (1) suffices; its existence is unknown.

For a direct back-map to the unchanged raw Kummer, take \(x=\beta r^2\) and use
\[
 t=\frac{4\beta r}{1-x},\qquad t'=\frac{2\beta r}{1+x},\qquad
 W=\frac{\beta^2\delta s(3+x)(1+3x)}{(1-x)(1+x)^2}.
\]
For \(f(z)=(z^2-\beta)(z^2+3\beta)\), the first factors are \(t^2-\beta=-\beta F/(1-x)^2\) and \((t')^2-\beta=-\beta(1-x)^2/(1+x)^2\); the second factors have the common numerator \(\beta(3+x)(1+3x)\) and the respective squared denominators. Thus \(W^2=\delta f(t)f(t')\) with the same coefficient \(\delta\). All denominators, \(t,t',W\) are nonzero; the original raw inverse gives \(s_{\rm original}\ne0\) and two nonzero ordinates. This is the same Γ map with the displayed signs.

## Primitive balanced charts and exact visible branches

Write a prospective \(r=N/M\) with positive coprime integers \(M,N\); signs may be changed because (1) is even. Let \(g=\gcd(M,\beta),\ e=\beta/g,\ M=gX\). Substitution in the binary quartic removes the square factor \(g^2\). The exact residual problem is
\[
       g^2X^4-18\beta X^2N^2+e^2N^4=\theta Y^2,\qquad
       \gcd(gX,N)=\gcd(e,X)=1 .                            \tag{2}
\]
Here \(Y\) is a nonzero integer: a rational square times squarefree \(\theta\) cannot be integral with a nontrivial reduced denominator. Conversely any (2) gives (1) by \(r=N/(gX)\) and the rational square relation between \(\delta\) and \(\theta\). The reciprocal \(r\mapsto1/(\beta r)\) transforms \(F\) by the square \(1/(\beta^2r^4)\), and sends \((g,e,X,N)\mapsto(e,g,N,X)\) with primitivity unchanged. Thus it suffices to choose the 128 divisors \(g\) with \(g<\sqrt\beta\); the maximum of \(X,N\) is unchanged by the reciprocal.

At each of the four already established odd-depth primes \(p\mid\theta\), both \(\beta\) and 5 are square units. Both \(M,N\) must be units, since a zero of one only would give a nonzero residue in the original binary quartic. Factoring over \(\mathbf Q(\sqrt5)\) gives
\[
 M^4-18\beta M^2N^2+\beta^2N^4
 = (M^2-\beta(2+\sqrt5)^2 N^2)(M^2-\beta(2-\sqrt5)^2N^2).
\]
Consequently \(M/N\pmod p\) lies in exactly the four choices \(\pm\sqrt\beta(2\pm\sqrt5)\). No assertion about unseen factors of \(\theta\) follows.

## Exact low-height conclusion by rational reconstruction

The product of the four literal primes is \(P=35589230039008870789\) and \(L=\lfloor\sqrt{(P-1)/2}\rfloor=4218366392\). Suppose \(X,N\le L\). For a fixed \(g\) each of the 256 CRT outputs \(a=M/N\pmod P\) gives at most one positive primitive candidate in this box: \(X/N\equiv a/g\pmod P\), and the difference of two cross-products has absolute value at most \(2L^2<P\). The usual Euclidean reconstruction is complete: with the reduced residue \(v=a/g\pmod P\), write \(vN-X=kP\). Then \(\gcd(k,N)=1\) since \(N\) is a unit mod \(P\) and \(\gcd(X,N)=1\), and \(|v/P-k/N|\le L/(PN)<1/(2N^2)\). By the continued-fraction approximation criterion, \(k/N\) occurs as a convergent. Stop at the first nonzero absolute remainder at most \(L\); its denominator in the Euclidean column is at most the denominator of any later convergent. If a valid candidate exists, this first vector and it have both coordinates of absolute value at most \(L\), so the cross-product argument makes them proportional; primitivity of the candidate and the bound on the first denominator force equality up to sign. The zero remainder cannot occur before a valid nonzero \(X\).

Filtering the reconstructed ratios by sign, primitivity and positivity of (2) leaves exactly 6110 candidates. At each of thirteen specified small scalar places, use the literal compact source to evaluate the unit \(\delta\) mod p. At \(p=7\) use the separately checked singular-arm specialization \(c\equiv1,\delta\equiv6\); the other twelve reductions are recomputed by finite group operations on the original \(h\) and source shift. Each shortening exponent is first verified to annihilate the actual input point on every required arm; \(c\) comes from the same chart norm. A candidate for (2) must have its left side times \(\delta\) square or zero mod each such p. This follows from the actual rational square condition, since \(\delta\) is a local unit at these p and the left side integral. The exact survivor counts are
\[
 6110,1538,610,372,191,109,49,22,12,7,5,3,2,0 .
\]
Thus **any Γ point must have normalized height \(\max(X,N)>4218366392\)** in (2). This does not rule out actual rational points or establish local admission for the actual Γ at unseen θ primes. No extra prime, θ factor, odd-p rank, or other pole is supplied.

Replay with Python 3: run replay_sparse_quartic.py and compare the output to EXACT-SPARSE-CRT-CONTROLS.json. The synthetic reverse-map calibration is not a Ready pole.
