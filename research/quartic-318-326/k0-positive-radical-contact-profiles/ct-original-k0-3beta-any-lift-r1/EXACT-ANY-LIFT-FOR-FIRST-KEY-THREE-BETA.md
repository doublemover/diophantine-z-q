# Exact factorization-free certificate for any lift of the first key \(3\beta\)

This paper concerns the **actual** full Sel₂ projection of the unchanged \(k=0\) Jacobian of any numerical Ready pole, not merely its isogeny-Selmer image. It sharpens the [specific norm lift with second slot -1](../ct-original-k0-first-character-r1/ACTUAL-K0-FIRST-CHARACTER-AND-EXACT-LIFT.md). No existence is asserted for the literal original scalar.

Write \(\mu=b/17=A/D^2\) reduced, \(A=\beta a^2\) with \(\beta\) positive squarefree, \(C=D^2-A\), \(B=A+3D^2\), and \(M=B/3\). The actual auxiliary curve is \(J:y^2=x(x-4A^2)(x-AB)\), with ordered Kummer triples. Ready ensures \(C\) odd and prime to 3, \(\beta\) odd and prime to 3, and \(M>0\) odd with \(3\nmid M\). Assume \(\theta=[C]\) nonsquare for the intended mark. The property “first slot \(3\beta\) occurs in full Sel₂” is equivalent to the following certificate.

1. Supply \(X,Y\in\mathbb Z\) with \(C=X^2-3Y^2,\ \gcd(X,Y)=1\). This certifies the first projection admits \(3\beta\) everywhere, by the exact primitive norm equivalence in the cited first-character paper.
2. Supply a signed odd squarefree integer u. Its positive prime support is contained in \(3\beta C\) (equivalently \(|u|\mid 3\beta C\)), and its actual local classes satisfy:
   - at 2, \(u\in[1],[5]\);
   - at 3, \(u\in[1],[3]\);
   - at every \(p\mid\beta\), \(u\in[1],[-3\beta]\).
   These tests only need the fixed \(\beta\)-support, not the factorization of C or of B.
3. Let \(a_*\) be the part of a prime to \(6\beta\), obtained by dividing out the entire part supported there. Give a square root of u in
\[
       (\mathbb Z/a_*\mathbb Z)[T]/(T^2+3\beta)
\]
and a square root of \(-u\) in
\[
       (\mathbb Z/M\mathbb Z)[T]/(T^2+1).
\]
A modulus 1 condition is vacuous. A certificate consists just of two integer coefficients in each ring, checked by expanding and reducing modulo the integer modulus.
4. Give integers \(r,s,w\), \(w\ne0\), with
\[
                  r^2+u s^2=M w^2.
\]
This last equation is a different conic for general u, not an assertion that M itself is a Gaussian norm.

The certified lift is precisely \((3\beta,-u,-3\beta u)\) in squareclasses. A nonzero marked Cassels sign for this lift depends only on its first slot and equals \((3\beta/D)\). If no u can meet the tests, the key \(3\beta\) does not lift, but there may be other first keys. A zero sign or absence of this key does not prove the marked torsor rational.

## 1. Literal local tests for every possible u

The first key \(3\beta\) already forces each \(p\mid C\) to split \(\sqrt3\) (including even-depth primes). Once this is so, at every \(p\mid C\) the whole local second coordinate group is available: the first root is a singleton and the colliding roots are a common **square** unit, so the first Kummer class is always trivial; the four-element local Kummer image then fills all pairs \((1,d,d)\). We use the odd local index-four theorem for full rational 2-torsion, hence do not require that the torsion rows themselves be independent at even-depth C primes.

After the first key is fixed, any second coordinate can be written as \(-u\) with u signed squarefree. At \(p\mid\beta\), at 3, and at 2 the baseline row \((3\beta,-1,-3\beta)\) is actually admitted and the differences between rows with the same first coordinate are exactly the local pure-second classes. The two independent odd torsion rows give \(\{[1],[-3\beta]\}\) at \(p\mid\beta\), and \(\{[1],[3]\}\) at 3; the dyadic calculation with \(\mu\) square and even depth \(m\ge4\) gives \(\{[1],[5]\}\). At infinity either sign is allowed in the second slot for positive first, by taking \(x>AB\) or \(0<x<4A^2\).

At an odd \(p\mid A,\ p\nmid\beta\), divide x/y by the even-valuation scale as in the earlier local proof. The first two roots collide to even depth, with singleton third root whose difference from the cluster has unit class \(-3\beta\). The singleton valuation is always even. Since the fixed first key is a unit, the second valuation is also even. Thus p does not occur in u. If \((-3\beta/p)=1\), the singleton third *class* is square, so the correction u must be square. If \((-3\beta/p)=-1\), all four unramified triples occur at even collision depth (the earlier nonsplit-node calculation), so no condition remains on its unit class.

At \(p\mid B,\ p\ge5\), the singleton is slot 2, so p cannot occur in u. The first coordinate \(3\beta\) has local class \([-1]\), because \(A\equiv-3D^2\) and \(\beta=[A]\). If \(p\equiv1\bmod4\), the singleton class is square and \(-u\) must be square. If \(p\equiv3\bmod4\) and collision depth is even, the entire unramified space is available. If \(p\equiv3\bmod4\) and collision depth is odd, the unramified image is just the equal-cluster unit line: before the collision depth the two clustered squareclasses agree; at or after it their smaller valuation is odd, so an all-unit triple cannot have nonsquare singleton. The fixed first \([-1]\) is available on that line, and again \(-u\) must be square. Thus the exact B condition is
\[
    (-u/p)=1\quad\text{for }p\ge5,\ p\mid B
         \text{ with } p\equiv1\bmod4\text{ or }v_p(B)\text{ odd}.
\]
Every other finite prime \(p\ge5\), including \(p\mid D\), is good and all full Kummer tuples are unramified there. These cases prove the support bound and are a necessary and sufficient set of local tests for the chosen u.

## 2. From the local tests to the finite and rational norm certificates

At primes of \(a_*\) the first quadratic algebra in the statement is étale. Where \(-3\beta\) splits modulo p, a scalar u is square over it exactly when u is square in the base residue field. At nonsplit primes the residue field is \(\mathbb F_{p^2}\), in which all scalars from \(\mathbb F_p^\times\) are squares. Every requested unit root lifts by Hensel at odd p (and by CRT across prime powers). This exactly gives the required even A conditions without factoring \(a_*\). Likewise the second quadratic algebra, at primes of M, is étale with square root of \(-1\) split or inert according to \(p\bmod4\). Its square-root condition covers the split-prime part of the B test, unconditionally in the exponent of that prime. Units are legitimate: \(M\) is prime to \(u\) by its support and the disjointness of B from \(\beta C\) at odd p≥5, with \(3\nmid M\).

For the exponent-odd part, use the local norm condition for \(M\) from \(\mathbb Q(\sqrt{-u})\). At \(p\mid M\) the latter is split or unramified, and \(M\) is a norm iff \(-u\) is square or its valuation at p is even. No new local norm obstruction appears away from M:
- At 2, \(M=D^2+A/3\equiv1\bmod8\) is a square unit, and at 3 it is a square unit because \(v_3(A/3)\ge1\).
- If \(p\mid u\) lies in \(\beta\), \(M\equiv D^2\bmod p\); if it lies in C then \(M\equiv(4/3)D^2\bmod p\) is square by the already certified \(C\) split condition. These square units are local norms even at ramified p.
- Outside these sites both values are units at unramified places, and at infinity M is positive. Split cases cause no restriction.

Thus the odd-exponent test is **equivalent** to \(r^2+u s^2=Mw^2,\ w\ne0\): Hasse–Minkowski for the ternary form gives the rational norm, then clear denominators. If \(-u\) is nonsquare, a nonzero solution cannot have \(w=0\); for \(-u\) square the split norm is already explicit. Together with the finite ring test this proves the exact B conditions and the full-lift equivalence. A modest certificate is verifiable using only integer multiplication, modular congruences, gcd, and the fixed local \(\beta\) rows; it does not require enumerating the astronomical source supports.

## 3. Nontrivial exact example and what remains literal

For a numerical Ready example take \(\beta=17,\ A=2448,\ D=115\). Then
\[
 C=10777=13\cdot829=110^2-3\cdot21^2,\quad
 M=14041=19\cdot739,\quad a_*=1 .
\]
The specified earlier second slot -1 fails because M is not Gaussian: 19 and 739 are \(3\bmod4\) at odd depth. But \(u=829\) satisfies the support and all small-place rows; \(829\equiv5\bmod8,\ 829\equiv1\bmod3\), and it is a nonzero square modulo 17. Also
\[
     2136^2\equiv-829\bmod14041,\qquad
     597^2+829\cdot20^2=14041\cdot7^2.
\]
Hence the actual alternate lift \((51,-829,-51\cdot829)\) is genuine, with marked sign \((51/115)=-1\). This is a numerical Ready instance, not a fold output; it demonstrates that the Gaussian norm is necessary for the earlier specific lift only, not for some lift of \(3\beta\).

For the original a=0 scalar at its own admissible h, these certificates have not been furnished; the existing finite evidence on the first projection and the residual denominator Jacobi factor remains as in the preceding first-character packet. This is a precise test of that key, not an inference of the marked radical or a direct PointPair.

Replay: python3 -B verify_any_lift_control.py | cmp - EXACT-ANY-LIFT-CONTROL.json. No Lean build or remote writes.
