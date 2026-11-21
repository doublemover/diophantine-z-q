# One Jacobi symbol rejects the literal fixed-pole k=0 point

This is a paper theorem for every genuine linear-denominator-prime Ready detector pole, plus a demonstrably nonvacuous arithmetic family at the same seven-prime support profile. The examples in §4 are **not** outputs of the original fold. The theorem tests the **unchanged numerical pole** and the **k=0 direction**, not all norm directions, not another representative in its two squareclasses, and not the rank of either selected twist.

Take the same `b` and coordinates as in the [first exact k=0 packet](../ct-original-k0-direct-isogeny-r1/LITERAL-K0-JACOBIAN-AND-DUAL-SEARCH.md). Write
\[
 0<\mu=b/17=A/D^2<1,qquad (A,D)=1,qquad C=D^2-A>0,qquad \delta=C/D^2.
\]
Here D is the **positive square root of the actual reduced denominator**, not a free scale, and C is the actual numerator of \(\delta\). Exclude C a square, for which the original direct two-zero-ordinate solution is separately available. The [literal linear-q source and contact calculation](../../joined-work-20261120/linear-denominator-prime-small-marked-selmer-r1/ACTUAL-LINEAR-Q-MARKED-SEL2-WITH-FEWER-AUXILIARIES.md) give
\[
 \beta=\operatorname{sf}(A)=17\prod_{p\in \mathcal P}p,
\quad \mathcal P=\{p_0,p_1,p_2,p_3,p_4,q\},
\quad p\equiv1\pmod{408}\ (p\in\mathcal P).
\]
In particular every contact is reciprocal-square with 17. In the source \(v_p(A)=1\) at the six contacts; the obstruction only needs odd depth. At 2 and 3, A has positive even valuation and D a unit; at 17, A has positive odd valuation and D a unit. These are consequences of the actual numerical Ready guards, not choices of a new b.

**Result.** If \(\eta=(d_1,d_2,d_3)\in\operatorname{Sel}_2(J)\) has each \(d_i\) a positive squarefree divisor of \(\beta\), in the literal split Kummer order 0,4A²,A(A+3D²), then
\[
  \langle (1,C,C),\eta\rangle_{\rm Cas}=\left(\frac{D}{d_1}\right) \in \{+1,-1\}.
\]
In particular a minus sign rules out a rational point on the actual integer quartic
\[
 z^2=C(U^2+3AV^2)^2+16A^2U^2V^2,
\]
and even a Selmer-4 lift of its marked class. Section 3 gives an **exact six-column** linear test for a sufficient class \((d,1,d)\), with no factorization of A+3D², conic-solving routine, or claimed upper bound on the full Selmer group.

## 1. Same integral Jacobian and all three rational tangent choices

Scale the original Jacobian x/y by D⁴/D⁶. The actual split Jacobian now has roots \(e_1=0,e_2=4A^2,e_3=A(A+3D^2)\) and \(e_3-e_2=3AC\). Its marked class is \((1,C,C)\), represented by
\[
 z_1^2-Cz_2^2=4A^2t^2,\quad
 z_1^2-Cz_3^2=e_3t^2,\quad
 z_2^2-z_3^2=3At^2.
\]
In order i=1,2,3 the conic omitting \(z_i\) has rational point
\[
  (1,1,0),\quad (3D^2-A,3D,1),\quad (2A,0,1),
\]
with coordinates in the indicated two z slots followed by t. For the middle point the norm identity is
\[
 (3D^2-A)^2-C(3D)^2=(D^2-C)(4D^2-C)=A(A+3D^2).
\]
Use the following tangent forms, with the common projective coordinates:
\[
 L_1=z_2-z_3,\quad L_2=(3D^2-A)z_1-3DCz_3-e_3t,\quad L_3=z_1-2At.
\]
By [Cassels, Second descents for elliptic curves, §7](https://doi.org/10.1515/crll.1998.039), in the split case the sign is the product over v,i of the local Hilbert symbol \((L_i(P_v),d_i)_v\), using local points avoiding the tangents. See the [explicit split formula (2.2)–(2.5)](https://zhangshenxing.github.io/publications/WangZhang2022.pdf) and [Fisher, The Yoga of the Cassels–Tate Pairing, Theorem 5.2](https://www.dpmms.cam.ac.uk/~taf1000/papers/casselspairing.pdf) for comparison with arithmetic Cassels–Tate. A rational Kummer image lies in the kernel, as does an image from Sel₄. The integer Jacobian change above multiplies the old three tangent forms by D,D⁴,D², respectively, if the old directions are used. This does not change the global product; accounting for it is important if using an old **local** tangent.

## 2. Exact local evaluation

For odd \(p\mid\beta\), the J-torsion Kummer classes at 0 and \(4A^2\) have parity patterns (1,0,1), (0,1,1). They therefore span the entire four-element local Kummer image. Here −1 is square and C is a unit square since \(C\equiv D^2\); the two classes are exactly
\[
 (h_p,1,h_p),\ (1,h_p,h_p),\qquad h_p=[3A]=[3\beta]\ \text{in }\mathbb Q_p^\times/\mathbb Q_p^{\times2}.
\]
Indeed \(A+3D^2\) has class 3 at such p. At p=17 the unit class of \(h_p/p\) is nonsquare (3 nonsquare, all six other primes square). Removing the 17 factor from a divisor of β produces a square unit at 17. Thus admissibility excludes 17 from *every* d_i. It follows all d_i are local squares at 2 (1 mod 8), 3 (1 mod 3), 17, and infinity (positive).

At a contact \(p\in\mathcal P\), take \(P=(s,1,-1,0)\), where \(s^2=C\) and \(s\equiv D\bmod p\). It has \((L_1,L_2,L_3)\equiv(2,6D^3,D)\bmod p\), all units. Both 2 and 6 are squares modulo such p, so the local product is \((D/p)^{v_p(d_2)+v_p(d_3)}=(D/p)^{v_p(d_1)}\).

All other finite places p≥5 have every d_i a unit. If p divides A, use the same point and unit tangents regardless of the valuation parity of A. If p divides C, use
\[
 t=L_1=1,\quad z_2=(1+3A)/2,\quad z_3=(1-3A)/2,\quad
 z_1^2=4A^2+Cz_2^2,\quad z_1\equiv-2A\bmod p.
\]
These satisfy the cover equations and give \(L_2\equiv-8A^2,L_3\equiv-4A\), both units. If p divides \(A+3D^2\), then \(C\equiv4D^2\); use again \(P=(s,1,-1,0)\) with \(s\equiv2D\bmod p\), giving residues \((2,24D^3,2D)\), all units. These three cases are pairwise disjoint for p≥5. In each case the symbols between units are trivial.

At all remaining p≥5 (including p|D), A,C,e₃ are units and the roots are distinct modulo p. One may see directly that every nonzero tangent value at a primitive local point has even valuation. For L₁,
\((z_2-z_3)(z_2+z_3)=3At^2\);
if L₁ is nonunit, \(z_2+z_3\) is a unit, since otherwise the equations force all four coordinates into p. For L₃ use \(L_3(z_1+2At)=Cz_2^2\) similarly. For L₂ put
\[
 a_0=3D^2-A,\quad b_0=3D,\quad
 r=a_0z_1-Cb_0z_3,\quad s_0=b_0z_1-a_0z_3.
\]
Then \(L_2(r+e_3t)=Cs_0^2\) by the same norm identity. If L₂ is nonunit and t is nonunit, then r and s₀ vanish modulo p, and the determinant −e₃ forces both z₁,z₃ to vanish modulo p, hence z₂ too. Thus t and \(r+e_3t\) are units in the nonunit L₂ case. This proves even evaluation orders. At all p there are local points by the original k=0 all-place proof; a local point can be moved off any tangent zeros on the smooth characteristic-zero cover. Its projective scaling does not change the product because \(d_1d_2d_3\) is a square. Hence no other place contributes and the product is exactly the claimed Jacobi symbol.

## 3. A tiny exact admission matrix, not a guessed extra Selmer class

For \(d=\prod_{p\in\mathcal P}p^{x_p}\), the tuple \((d,1,d)\) is in the actual full Sel₂(J) if and only if:

1. \(x\) lies in the kernel of the known six-contact Legendre Laplacian; row p means
   \[
   \left(\frac{d/p^{x_p}}{p}\right)=\left(\frac{\beta/p}{p}\right)^{x_p}.
   \]
   In the source graph the \(p_i,p_j\) nonsquare edges are the two fixed 7-edges XOR the common epsilon bit; all five q-links have that epsilon bit. After dropping the isolated 17, kernel dimensions are 4/3 in the plus/minus phases. The actual local torsion evaluation above gives precisely these rows, not just their necessity.
2. \((d/p)=+1\) at every prime p≥5 dividing C.
3. \((d/p)=+1\) at each prime p≥5 dividing A with p not dividing β and \((-3\beta/p)=+1\).

For the last two claims use this direct odd-place local fact. Suppose exactly two integral roots collide modulo p, with depth m, and let γ be their common residue minus the separate root. In the three ordered Kummer slots, the unramified line consisting of equal unit classes in the clustered slots and 1 in the separate slot is always present. To see its nontrivial element, choose residue x of the form \(e_{\rm sep}+u^2\) making the two clustered factors nonsquares: \(\sum_u \chi(u^2-\gamma)=-1\) gives such a u with nonzero clustered factors. For \(u\ne0\) lift any such x by Hensel. For u=0 use the actual separate-root torsion with its two nonsquare factors and square exceptional factor. If γ is square, the separate slot is always square (outside the cluster the other factors have square product, inside the cluster the separate factor has residue γ), so the unramified line is exact. If γ is nonsquare and m is even, every local Kummer valuation is even. For 0<r<m the two clustered factors have equal valuation and same unit class, making their product square and the separate factor nonsquare, impossible. With one clustered depth at least m, the smaller clustered depth is m, and the cubic square forces the other clustered depth even too. Away from their cluster, the two clustered factors have even valuation (this includes negative x-depth by the cubic square condition). The all-unit image is then the full two-dimensional unit space since the local image has order four at odd p. The same reasoning applies to torsion by continuity of Kummer classes, or by their direct exceptional values.

For p|C the separate root is 0 and γ=4A² mod p is square, so the extra condition on d is exactly row 2. For p|A, p∤β put \(m=v_p(A)>0\), even. Rescale x/y by \(p^m,p^{3m/2}\). The first two roots now collide to depth m and the separate third root has residue \(3D^2(A/p^m)\), so γ has class \(-3\beta\). This proves row 3, with no row if γ is nonsquare. At p|A+3D² the separate slot is slot 2, already 1 for our tuple; the always-present unramified line gives local admissibility whether γ is square or not. No factorization of this integer is needed. Good odd places have the full unramified image for split rational 2-torsion (smooth reduction, finite-field Kummer of size four, and the prime-to-p formal group uniquely 2-divisible); all unit coordinates qualify. The small, infinite, and contact sites have already been handled. Thus these are both necessary and sufficient rows.

One can either find a kernel vector with odd dot product with the row \(((D/p))_{p\in\mathcal P}\), using GF(2) symbols, or verify one supplied d. No positive conclusion if this row annihilates the kernel; other Cassels test classes may involve different support. This is a rejection criterion, not a substitute for a \(k=0\) rational point.

## 4. Nonvacuity at every fixed allowed profile, without source-realization claim

Fix **any** seven-prime support profile above; set \(d=\prod_{p\in\mathcal P}p,\ \beta=17d\). The constant contact vector satisfies all Laplacian rows. There are infinitely many rational b with exactly this β, the original numerical Ready guards, and the six depth-one contacts, for which the test rejects. This shows why the known β and its complete Legendre table alone cannot force the k=0 direction.

Start with \(a_0=12\) (this seed scalar is unrelated to the tangent coefficient in §2). Pick a positive integer \(r\), and put \(Y=12r\), targeting
\[
 A=17d a^2,\quad D=d+17(a/2)^2-36r^2,\quad
 X=D-2d,\quad C=D^2-A=X^2-dY^2.
\]
Choose \(r\equiv0\bmod17\); at each \(p\mid d\) prescribe
\(\left(\frac{17(12/2)^2-36r^2}{p}\right)\) to be +1 except one −1. This is possible because 17 is square there, and the quadratic polynomial over Fₚ takes both nonzero square classes: the character sum is −1 and there are just two zeroes. At each prime dividing \(17(12/2)^2-d\), impose r ≡1. These latter primes are disjoint from 17 and d, and the CRT gives a positive r. The sum identity follows by counting factorizations \((u-v)(u+v)=\gamma\) with \(\gamma\ne0\) over Fₚ.

Now set \(a=12\cdot2^{M k}\) with positive M divisible by the orders of 2 modulo all odd primes dividing dr. This preserves a modulo all needed odd moduli. For k sufficiently large, D,X>0 and \((X-1)^2<C<X^2\), so C positive nonsquare. D and X are units mod 2 and 3. If a prime divides r then X is nonzero mod that prime, by the imposed coprimality and preserved seed residues (also at 17); hence \((X,Y)=1\). D is a unit at 17 because \(D\equiv d\) there, and at the six contacts by their prescribed signs. It follows \((A,D)=1\) and every p≥5 dividing C is split in \(\mathbb Q(\sqrt d)\): if it divided Y it would divide X, and it cannot divide d. Row 3 is empty, since **only** 2 and 3 can divide a. Thus \((d,1,d)\) is a genuine Selmer class with \((D/d)=-1\).

For these b=17A/D², \(0<b<17\), the reduced denominator is square, and the local square guards follow from \(b=d(17a/D)^2\) and d being locally square at 2,3,17. Its valuations at 2,3,17 are \(2v_2(a)\ge4,2,2\), and all six contacts are depth one. The resulting b values are distinct for all sufficiently large k (A grows like a², D like a² and the ratio decreases to zero). These are infinite **arithmetic profiles with certified k=0 failure**, not new rational fold outputs, not a proof that any literal pole in the specific original linked family has the failing sign, and not a no-PointPair result.

## Replay and independence

`python3 -B verify_contact_cassels.py | cmp - EXACT-CONTACT-CASSELS.json`.
The finite replay checks both graph dimensions, proves nonvacuity via primitive norm witnesses on **both** prescribed phase graphs, and checks projective tangent identities independently. It does not evaluate a numerical original `(h,t)` source. No Lean build or remote write.
