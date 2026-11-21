# An exact numerical Ready family with the full marked Cassels sign trivial

This positive construction, independently arithmetic checked, works for every allowed detector \(\beta\)-profile and both contact phases. It concerns numerical Ready poles, varies the companion \(\theta\), and does not produce a literal fold output or a rational point. The result is **Sel₄ admission of the marked k=0 class**, not rational solubility. The construction is credited as the proposed positive-profile construction, not an application of a rank converse.

Fix the six contact primes \(p_0,\ldots,p_4,q\) of the [original linear-q profile](../../joined-work-20261120/linear-denominator-prime-small-marked-selmer-r1/ACTUAL-LINEAR-Q-MARKED-SEL2-WITH-FEWER-AUXILIARIES.md) and \(\beta=17p_0\cdots p_4q\). For an integer \(j\ge0\), use
\[
 K=18\beta\,2^j,\quad \Delta=2K^2-12\beta,\quad L=\Delta-1,\quad S=\Delta+1,\quad
 D=S^2,\quad a=24L,\quad A=\beta a^2 .
\]
Require \(\Delta>2304\beta\); arbitrarily large j are available. Set \(b=17A/D^2,\ C=D^2-A,\ B=A+3D^2\). The variables D and A will be the **reduced** denominator square root and numerator of \(\mu=b/17\).

### Actual Ready guards and exact squareclasses

K is even, \(\Delta\equiv4\bmod8\), so L,S,D are odd. At 3 and every prime of \(\beta\), \(\Delta\equiv0\) so \(L\equiv-1,\ S\equiv1\). The gcd of L and S divides 2, thus is one; also S is prime to \(24\beta\). Hence \(\gcd(D,A)=1\). Each of the six contacts has valuation exactly one in \(A\) and thus in the pole b. The local valuations of b at \(2,3,17\) are respectively \(6,2,2\). At those places \(b=17\beta(a/D)^2\) is a square: all contact primes are \(1\bmod408\), so \(17\beta\) has square unit class in \(\mathbb Q_2,\mathbb Q_3\) and stripped square class in \(\mathbb Q_{17}\). The reduced denominator \(D^2\) is square because D is prime to 17, and the exact squarefree first class of \(\mu\) is \(\beta\).

In fact C is positive nonsquare. Put \(z=D-288\beta>0\); since \(L^2=D-4\Delta\),
\[
 C-z^2=2304\beta(\Delta-36\beta)>0.
\]
For \(\Delta>2304\beta\) this is less than \(\Delta^2\), while \(2z+1=2(\Delta+1)^2-576\beta+1>\Delta^2\). Thus \(z^2<C<(z+1)^2\), and \(0<b<17\). This is not the trivial companion-square case.

### Why the **whole** marked pairing vanishes

There is the primitive norm identity in \(\mathbb Z[\sqrt{-2}]\)
\[
       B/3=(D-2L^2)^2+2(4KL)^2 .
\]
Indeed \(L^2-D=-4\Delta=-8K^2+48\beta\), so expansion yields \(D^2+192\beta L^2=D^2+A/3\). For primitivity the first norm coordinate is odd. At an odd p dividing L it is \(D\equiv4\bmod p\); at an odd p dividing K (necessarily 3 or a prime of \(\beta\)) it is \(-1\bmod p\). Thus the coordinates have gcd one. Consequently every odd prime factor of \(B/3\) splits \(\sqrt{-2}\): reducing the primitive norm at a prime divisor gives a nonzero root of \(-2\).

For the literal marked class \(\Lambda=(1,C,C)\) on the \(k=0\) Jacobian of this numerical pole, the [full first-coordinate formula](../ct-original-k0-first-character-r1/ACTUAL-K0-FIRST-CHARACTER-AND-EXACT-LIFT.md) gives on **every genuine Sel₂ test class** \(\eta\) with first coordinate \(d_1\)
\[
       \langle\Lambda,\eta\rangle=(d_1/D)
           \prod_{p\ge5,\ p\mid B}(-2/p)^{v_p(d_1)}=+1 .
\]
The denominator D is an integer square and \(\gcd(d_1,D)=1\); the other factors are + by the primitive norm. No finite support approximation to the pairing is used. It follows that \(\Lambda\) is in the Sel₄ image by the standard Cassels radical theorem ([Fisher, On binary quartics and the Cassels–Tate pairing, §1](https://doi.org/10.1007/s40993-022-00376-z)). This does not imply a rational \(k=0\) point, and neither the literal scalar nor a shared four-pole grid has been produced.

Replay: python3 -B verify_positive_radical_profiles.py | cmp - EXACT-POSITIVE-RADICAL-PROFILES.json. Both exact arithmetic phase inputs, their \(\beta\) graphs, Ready depths, C between squares and the literal primitive norm are verified without factoring B. No Lean build or remote write.
