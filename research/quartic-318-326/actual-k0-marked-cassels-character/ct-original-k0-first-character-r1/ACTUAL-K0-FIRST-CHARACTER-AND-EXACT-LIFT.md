# Full first-coordinate Cassels character and one concrete lift test

**Scope.** For every numerical Ready pole, this computes the actual marked Cassels sign on every genuine full 2-Selmer class of the literal \(k=0\) Jacobian. Then two integer norms certify one specified full lift of a first coordinate. Source membership and rational points are not inferred from a zero sign. Statements on the original scalar concern its own admissible index, not a completed grid.

Let \(0<\mu=b/17=A/D^2<1\) be reduced with \(D>0\), and put
\[
 C=D^2-A>0,\quad B=A+3D^2>0,\quad
 \beta=\operatorname{sf}(A),\quad
 J:y^2=x(x-4A^2)(x-AB),\quad \Lambda=(1,C,C).
\]
The same \(\Lambda\) is the \(k=0\) torsor [by the original Jacobian calculation](../ct-original-k0-direct-isogeny-r1/LITERAL-K0-JACOBIAN-AND-DUAL-SEARCH.md). Ready implies \(D\) is prime to \(2,3,17\), \(m=v_2(A)\ge4\) even with \(A\) square in \(\mathbb Q_2\), \(n=v_3(A)\ge2\) even with \(A\) of unit class 2 in \(\mathbb Q_3\), and \(v_{17}(A)\) is positive odd with stripped unit square at 17. In particular \(\beta\) is odd and prime to 3; 17 falls in the ordinary \(p\ge5\) case. C is odd, \(C\equiv1\bmod3\); B is odd with \(v_3(B)=1\). Assume C nonsquare for the nontrivial marked cover.

For every \(\eta=(d_1,d_2,d_3)\in \operatorname{Sel}_2(J)\), choose signed squarefree representatives, product a square. Then \(d_1>0\) is odd, coprime to D, and the exact global sign is
\[
 \boxed{\quad
 \langle\Lambda,\eta\rangle_{\rm Cas}
    =\left(\frac{d_1}{D}\right)
       \prod_{\substack{p\ge5\\p\mid B}}\left(\frac{-2}{p}\right)^{v_p(d_1)} .
       \quad} \tag{1}
\]
The first symbol is Jacobi (1 for \(D=1\)); exponents are ordinary valuations, only parity matters. A denominator prime is a good prime of this integral model. Membership forces \(d_1\) a unit there, not necessarily a square unit.

## 1. Full local proof and cancellations

Use exactly the explicit integral tangent points and \(L_1,L_2,L_3\) from the [contact formula](../ct-original-k0-contact-cassels-r1/ACTUAL-CONTACT-CASSELS-REJECTION.md). Since \(d_3=d_1d_2\) in squareclasses, the Cassels product at v is
\[
 (L_1 L_3,d_1)_v(L_2 L_3,d_2)_v.
\]
Divide each local sign by \((2\beta,d_2)_v\), whose global product is one. The adjusted sign is independent of the second coordinate at fixed local first coordinate by the [pure-second local identity](../ct-original-k0-pure-second-neutral-r1/ACTUAL-K0-PURE-SECOND-CASSELS-NEUTRALITY.md). All symbols use exactly these integral rational tangent forms. The formula and comparison are [Cassels, §7](https://doi.org/10.1515/crll.1998.039) and [Fisher, The Yoga of the Cassels–Tate Pairing, Theorem 5.2](https://www.dpmms.cam.ac.uk/~taf1000/papers/casselspairing.pdf).

* For \(p\ge5\) dividing A, take \(P=(s,1,-1,0)\) with \(s^2=C,\ s\equiv D\bmod p\). Product residues are \(L_1L_3\equiv2D\), \(L_2L_3\equiv6D^4\). If \(v_p(A)\) is even, rescale by the square \(p^{v_p(A)}\). The first two roots collide, the third is singleton, so \(v_p(d_1)=v_p(d_2)\bmod2\) since \(v_p(d_3)\) is even. As \(6\beta,D\) are units, the adjusted sign is \((6\beta D,d_1)_p\). If \(v_p(A)\) is odd, use actual torsion row exponent bits \(i,j\), so \(d_1=[3\beta]^i,\ d_2=[-1]^i[-3\beta]^j\). The residual ratio of \(L_2L_3\) to \(2\beta\) has class \(3\beta\), with \((3\beta,-3\beta)_p=1\) and \((3\beta,-1)_p=(3\beta,3\beta)_p\). Thus the sign is again \((6\beta D,d_1)_p\), **also at 17**. No choice of 17-adic square-root sign has been assumed.
* For \(p\ge5\) dividing C, \(d_1\) is square because \(4A^2,AB\) collide to a nonzero square residue. The adjusted sign is 1, by the explicit \(L_2L_3\equiv32A^3\) and \(\beta\) square here.
* For \(p\ge5\) dividing B, use \(s\equiv2D\bmod p\); thus \(L_1L_3\equiv4D,\ L_2L_3\equiv48D^4\), both units. The second slot has even valuation by singleton-root parity, so the adjusted sign is \((D,d_1)_p\). At this site \(\beta=[-3]\), so \((6\beta,d_1)_p=(-2,d_1)_p\).
* All other \(p\ge5\), **including those dividing D**, have distinct reduced roots on the integral model. The local coordinates are unramified and the actual integral tangent evaluations have even valuation by the three opposite-side tangent identities from the contact/pure-second proofs. Thus the adjusted sign is 1. This is not in general the sign of \((D,d_1)_p\) when \(p\mid D\).

At **3** the two torsion rows span (their valuation vectors are \((1,0,1),(0,1,1)\) since the nonzero root depths are \(2n,n+1\), with n even). Their first two local entries are \((6,-1)\) and \((1,3)\). At the chosen infinity point \(s=D u,\ u^2=C/D^2,\ u\equiv1\bmod9\), one has \(L_1L_3=[2D]\), \(L_2L_3=[6]\), and \(2\beta\) square. The second torsion row pairs trivially by \((6,3)_3=+1\). On the first row the adjusted sign is \((2D,6)_3(6,-1)_3=(D,6)_3\). Thus it is \((D,d_1)_3\), with \(d_1\) of local class 1 or 6. Also \(6\beta=[3]\) and \((3,6)_3=+1\).

At **2** divide x/y by \(2^m,2^{3m/2}\) so roots 0 and \(4A^2/2^m\) collide at depth \(m+2\), and the third root is a unit of class 3. The first slot always has even valuation. Negative x-depth is even by the cubic equation; depth 0 is already even. For positive odd depth 1, the first two factors have equal squareclass (their ratio is 1 modulo 8), and the last factor \(2u-3\bmod8\) for u odd is never square. For \(3\le r\le m-1\) odd the first two also have equal class, and the last factor has class 5. At the only remaining odd depth below \(m+2\), namely \(m+1\), the first two have equal valuation and their unit-class ratio is \(1-2v\equiv3\) or \(7\bmod8\) for odd v; neither can cancel the last class 5. Above \(m+2\), an odd valuation of x disagrees with the even valuation of the second factor, and the third factor is a unit. Thus all first classes are units. For each of the four unit classes \(d_1\) an actual representative has \(d_2=5d_1,\ d_3=5\): take x of depth **m** with prescribed stripped unit, giving second-factor ratio \(1-4\cdot\mathrm{odd}\) and last factor class 5. All other classes with the same first coordinate differ by the pure-second kernel. The exceptional torsion values comply by continuity of the local Kummer map.

Again choose \(u=\sqrt{C/D^2}\equiv1\bmod8,\ s=D u\). Then \(L_1L_3=[2D]\), \(L_2L_3=[2\lambda]\), where \(\lambda=7\) for \(m=4\) and \(\lambda=3\) for \(m\ge6\) (the exact two cases in the pure-second identity). With \(2\beta=[2]\) and \((\lambda,5)_2=1\), the adjusted sign is \((2D\lambda,d_1)_2=(6\beta D,d_1)_2\): the ratio class is 1 or 5 and \((5,d_1)_2=1\) for **any** odd unit \(d_1\). At infinity the first coordinate is positive since only nonnegative x can occur, and a positive \(s=\sqrt C\) gives positive tangent products and \(2\beta>0\). Negative \(d_2,d_3\) do not change the argument.

The adjusted product has factors \((D,d_1)_v\) only at \(2,3,p\mid A,p\mid B\), and \((6\beta,d_1)_v\) only at \(2,p\mid A\). By Hilbert reciprocity for the first constant, the missing terms are exactly \(p\mid D\), giving \((d_1/D)\); other sites are unit-unit, at C the first class is square, and infinity positive. For the second constant the missing terms are exactly \(p\ge5,p\mid B\), since 3 is trivial and at C the first class is square. At B it is \((-2/p)^{v_p(d_1)}\). These reciprocals equal themselves as signs. This proves (1). If \(d_1\) is contact-supported, that support is prime to B and its primes are 1 modulo 4, so \((d_1/D)=(D/d_1)\) recovers the earlier result. The case \(d_1=1\) is the pure-second neutrality.

## 2. The first-coordinate image and one exact factorization-free lift

The quotient tested is the **image** of the first-coordinate map from full \(\operatorname{Sel}_2(J)\), not automatically the whole dual-isogeny Selmer group. Use \(\phi:J\to J'\) with kernel the root 0 torsion, and \(\hat\phi:J'\to J\) with \(\hat\phi\phi=[2]\). By the split \(J[2]\) and Kummer functoriality, its first coordinate is the dual-isogeny connecting value x after \(\phi:J[2]\to J'[\hat\phi]\). A first key k belongs to \(\operatorname{Sel}^{\hat\phi}\) precisely when
\[
 N^2=k U^4-A(5A+3D^2)U^2V^2+(4A^3B/k)V^4
\]
is everywhere local, by \(x=k(U/V)^2\). This alone is only local first-coordinate admission. To lift globally one needs a common \(d_2\) in the intersection of the actual second-coordinate cosets over k at all places, with \(d_3=k d_2\). An admitted nontrivial sign prevents the **marked** class lifting to Sel₄; if the character is trivial on the **whole actual first image**, the mark belongs to the Sel₄ image by [the Cassels pairing radical theorem, as stated in Fisher §1](https://doi.org/10.1007/s40993-022-00376-z). This does not assume Sha finite and does not infer a rational point or a rank from Sel₄ admission.

The particular key \(k=3\beta\) belongs to the actual dual-isogeny Selmer group **iff** every \(p\mid C\) splits in \(\mathbb Q(\sqrt3)\). At those primes the first-coordinate square condition means \((3/p)=1\), since \(\beta\) is square. Away from C, actual torsion supplies k at \(p\mid\beta\) and at 3, and the 2-adic representative derives it at 2. At odd two-root collisions of A at even depth and of B the unramified equal-cluster unit line supplies either unit class in the first slot, regardless of the separate root's class. At good places all unit triples of square product occur. At infinity k is positive.

More strongly, the **specified** lift
\[
             (d_1,d_2,d_3)=(3\beta,-1,-3\beta)
\]
belongs to full \(\operatorname{Sel}_2(J)\) **iff**
\[
 \begin{array}{ll}
 \text{(i)} & \exists u,v\in\mathbb Z:\quad u^2-3v^2=C,\quad \gcd(u,v)=1,\\
 \text{(ii)} & \exists r,s\in\mathbb Z:\quad r^2+s^2=B/3.
 \end{array} \tag{2}
\]
This does **not** characterize existence of any other lift of \(3\beta\). At \(p\mid\beta\) and at 3 it is the first torsion row, at 2 the stated depth-m representative, and at infinity the sign \((+,-,-)\) is realized by \(0<x<4A^2\). At \(p\mid C\) it is the unramified equal pair iff (i)'s split test holds. At \(p\mid A,\ p\nmid\beta\), the singleton class is \(-3\beta\) after scaling. If square, the lift is the ordinary unramified line; if nonsquare, the full unramified space occurs at even collision depth. At \(p\mid B,\ p\ge5\), the singleton is slot 2 and \(\beta=[-3]\); the lift has classes \((-1,-1,1)\). At split primes for \(-1\) this is trivial. At nonsplit primes it is admitted exactly at even collision depth: off the cluster the singleton is square, on the cluster below collision depth both clustered factors have equal unit class, and at or above collision depth the lower valuation is that depth, which must be even for an all-unit tuple. The converse follows from the full unramified space at a nonsquare singleton and even collision depth, as in the contact calculation. Thus test (ii) requires \(v_p(B)\) even for all \(p\ge5,\ p\equiv3\bmod4\).

For (i), C is odd and \(C\equiv1\bmod3\). A primitive solution makes every \(p\mid C\) split because p cannot divide v without dividing u. Conversely \(\mathbb Z[\sqrt3]\) is the full ring of integers and has class number one (real quadratic Minkowski bound \(\sqrt{12}/2<2\)). With every prime of C split, choose one of the prime ideals over each p with exponent \(v_p(C)\). Their product is principal; its generator has norm \(\pm C\) and must have positive norm since \(u^2-3v^2\equiv u^2\bmod3\) and \(-C\equiv-1\). Choosing only one ideal over each p ensures \(\gcd(u,v)=1\). There are no 2 or 3 factors. For (ii), B is odd and \(v_3(B)=1\), so Fermat's two-squares theorem on the integer \(B/3\) gives exactly the even condition; no primitive pair required.

When (2) holds, (1) on this lift is \((3\beta/D)\), since the \(p\ge5\) support of \(3\beta\) is prime to B. A minus sign is a genuine global obstruction to the unchanged \(k=0\) cover. The two norms do not imply any sign by themselves.

## 3. Exact scalar cutoff and tests

For the [actual original a=0 scalar](../ct-actual-scalar-k0-supported-admission-r1/ACTUAL-SCALAR-SUPPORTED-K0-SELMER-CUT.md), the eight beta-prime rows have zero kernel on first coordinates supported by β. Allowing 3 adds exactly one potential nonzero vector: the all-one β mask, yielding \(3\beta\), since it solves the inhomogeneous row and the homogeneous matrix is injective. C primes never contribute first-coordinate support, and 2 is excluded by §1. Thus on support \(\{3\}\cup\operatorname{Supp}(\beta C)\) only \(3\beta\) remains to try. Its possible bit is \((3\beta/D)\) whether lifted as in (2) or otherwise; no lift is claimed on this scalar. Both documented actual C-primes 131,6551 split \(\sqrt3\), but unknown C primes might not. A same-class move preserving \(\theta=\operatorname{sf}(C)\) cannot remove a nonsplit prime of \(\theta\).

The [actual scalar denominator analysis](../../joined-work-20261120/rc-linked-scalar-higher-descent-r4/EXACT-TAU-COSETS-AND-AGGREGATE-L-TEST.md) establishes exponent one at the fixed denominator primes \(29,181,1346909,70850399941\). Their \((3\beta/p)\) signs are \(+,-,-,+\), product +. All other odd-exponent denominator primes split \(-1\) and \(-R_{\rm input}\); hence \(R_{\rm input}\) is square there. Since \(3\beta=[561 R_{\rm input}]\), the exact remaining symbol is \((561/D_{\rm exc})\) with \(D_{\rm exc}\) the squarefree product of the other actual odd-exponent denominator primes. Coarse split requirements on \(2,-1,7,-R_{\rm input}\) and the high 2-power congruence do not determine the independent character 561 (CRT gives both signs without claiming actual crossed poles). No expansion of the source or full value of the remaining bit is claimed.

The deterministic replay compares both previous exact contact profiles to \((d_1/D)=(D/d_1)\). It checks the B-term on actual rational torsion in a small numerical-Ready case \(A=2448,D=55\), whose \(B/3=23\cdot167\) has two individually negative \((-2/p)\) factors. Finally a full-lift numerical example at \(A=2448,D=67\) has \(C=2041=46^2-3\cdot5^2\) primitively, \(B/3=5305=72^2+11^2\), and \((51/67)=-1\). This is a genuine k=0 obstruction under numerical Ready, **not** a literal source scalar. The literal scalar claims here are the first-slot support cut, fixed denominator factors, and exact conditions for the future test.

Replay: python3 -B verify_first_character.py | cmp - EXACT-FIRST-CHARACTER-CONTROLS.json. No Lean build or remote write.
