# The first half of the raw level-48 detector trace is unmarked

For either actual balanced detector twist with the refinement \(n\equiv23\bmod24\), the raw level-48 trace descends to a point in \(4E_n(\mathbf Q)\). The key is the *same* coherent square root at two ramified primes, computed up to a common sign by a modular unit. No nonzero trace, rank, or rational marked point is asserted.

## 1. Selected hypotheses and one first-half discriminator

Let \(n>0\) be the selected squarefree twist. The original positive mark \(\beta=[17b]\) is represented by 17 times six distinct genuine contact/denominator primes and divides \(n\). The final selected \(q_0\mid n\) does not divide \(\beta\). Write
\[
 E_n:y^2=x(x-n)(x+3n),\qquad E_0:y^2=x(x+1)(x-3),\qquad
 D=-n,\quad K=\mathbf Q(\sqrt D).
\]
Let \(\mathfrak n=\mathfrak p_2^4\mathfrak p_3\) be the chosen level ideal, \(x_{\mathfrak a}\) the full oriented \(X_0(48)\) CM class orbit over the Hilbert class field \(H/K\), \(h=|\mathrm{Cl}(K)|\), and \(P=\sum_{\mathfrak a}\phi(x_{\mathfrak a})\) the raw trace on \(E_0\), with no averaging. The exact finite level map \(\phi\) satisfies \(\phi w_{48}=T_3-\phi\), where \(T_3=(3,0)\). Denote by \(P_D\) the twist descent, with abscissa \(x_D=Dx(P)\) when nonzero. The preceding rational-double result proves:
1. At every \(p\mid n,\ p\ne17\), inertia freely pairs the **characteristic-zero** class indices such that the two reduced \(\phi\)-values in a pair sum to \(T_3\). There are \(h/2\) pairs and \(4\mid h\), so \(\overline P=O\).
2. \(P_D\in2E_n(\mathbf Q)\). If it is not \(O\), then \(v_p(x_D)\) is even and nonpositive at all those primes.
3. The actual \(\mathrm{Sel}_2(E_n)\) in \((x+3n,x-n)\) coordinates is the direct sum of the rational 2-torsion image and the line \(M=(\beta,1)\).

The rational torsion is precisely \(C_2^2\). At 3 one has \(v_3(\Delta)=2\), \(v_3(c_4)=0\), \(-c_6=2240n^3\equiv1\bmod3\), so the model is minimal split \(I_2\). In its Tate uniformization \(\mathbf Q_3^\times/q^{\mathbf Z}\) with \(v_3(q)=2\), the valuation modulo two has kernel exactly \(\mathbf Z_3^\times\). That kernel has torsion \(\{\pm1\}\), so the local torsion has order at most four; all four global 2-torsion points already exist. Therefore a nonzero \(P_D\) is nontorsion: a rational double which is torsion would have a torsion half, killed by two. In the coordinate argument below require \(P_D\ne O\), the zero case being immediate for divisibility.

For \((x,y)=P_D\), choose rational roots \(r_0^2=x,\ r_1^2=x-n,\ r_3^2=x+3n\) with \(r_0r_1r_3=-y\). The split-root halving formula gives a rational half \(Q\) with \(x(Q)=x+r_0r_1+r_1r_3+r_3r_0\); all four halves are covered by compatible sign changes. In particular
\[
 x(Q)+3n=(r_3+r_0)(r_3+r_1),\qquad x(Q)-n=(r_1+r_0)(r_1+r_3).
\]
At each \(p\mid n,\ p\ne17\), the root valuations equal \(e=v_p(x)/2\le0\), and stripped root units have the same square modulo \(p\). If two stripped signs agree then \(v_p(r_i+r_j)=e\); otherwise it is \(1-e\), because \(v_p(r_i^2-r_j^2)=1\) and \(v_p(r_i-r_j)=e\). Thus the first Kummer parity of \(Q\) is zero exactly when the **one rational number**
\[
 \rho_Q=r_1/r_0=\sqrt{(x-n)/x}
\]
reduces to \(+1\). This is the coherent root for that half, not a separate root choice at each prime.

At each of these primes the torsion vectors from \((0,0)\) and \((n,0)\) have valuation pairs \((1,1)\) and \((1,0)\), respectively. The mark has zero pair at \(q_0\), first parity one at any genuine \(p_\beta\ne17\). Hence the first-half non-torsion mark coefficient is the difference of its first parities at \(q_0,p_\beta\). The two signs of the global root interchange the two residue signs simultaneously.

## 2. Exact modular unit and its lift

Put \(f_0=(x+1)/x\) on \(E_0\) and \(f=\phi^*f_0\). In [Colò, Appendix A, pp. 245, 247–248](https://www.leonardocolo.com/documents/thesis/PhD_Thesis.pdf), the chart has \(Y^2=X^8+14X^4+1\), \(y_{48}=(Y+X^4+1)/2\); one has \(x\circ\phi=y_{48}/X^2\), \(\pi_1^*x_{24}=1+y_{48}/X^2\). The poles of \(f\) are the double zeros of \(x\circ\phi\), at the minus branches \(X=0,Y=-1\) and \(X=\infty,Y/X^4=-1\). The long-coordinate divisors identify these branches as \(1/16,1/8\): \(1/16\) is the zero of \(y_{48}\), while among the poles of \(X\) only \(\infty\) is a pole of \(y_{48}\) and maps to \(O\). Atkin–Lehner sends the two pole cusps to \(1/3,1/6\) in some order, above \((-1,0)=T_3-(0,0)\). Thus
\[
 \operatorname{div}(f)=2[1/3]+2[1/6]-2[1/8]-2[1/16],
 \qquad f=\eta_2^{-1}\eta_4^2\eta_6^3\eta_8^{-3}\eta_{12}^{-2}\eta_{24}.\tag{1}
\]
Here \(\eta_d=\eta(d\tau)\). To see the eta identity directly, the exponent vector has weight zero, both Newman sums zero and \(\prod d^{r_d}=9/16\) a square. The [Newman and Ligozat formulas](https://pmc.ncbi.nlm.nih.gov/articles/PMC10447328/) give its cusp orders \(\frac{48}{24\gcd(c^2,48)}\sum_d r_d\gcd(c,d)^2/d\) for every cusp denominator \(c\mid48\), agreeing with the displayed divisor. The constant is fixed by the leading value 1 at \(\infty\), where \(\phi=O\). This avoids using the duplicated long-coordinate eta expression printed in the thesis.

Use the quotient isogeny \(\psi\) by \(T_3\) and its dual onto \(E_0\). Translating \(x\) on \(E_0\) by 3 gives the formulas
\[
 E^\sharp:v^2=u(u^2-14u+1),\quad
 \widehat\psi(u,v)=\left(x=3+\frac{v^2}{4u^2},\ y=\frac{v(1-u^{-2})}{8}\right).
\]
The signs of \(\psi,\widehat\psi\) are chosen so their composite is \([2]\). The rational kernel of \(\widehat\psi\) is \(\{O,T^\sharp\}\), \(T^\sharp=(0,0)\). Define \(R=(u-u^{-1})/(4(x\circ\widehat\psi))\). The equation of \(E_0\) gives \(R^2=f_0\circ\widehat\psi\), by writing \(R=y/(x(v/(2u)))\) in the function field. Translation by \(T^\sharp\) sends \(u\) to \(1/u\), and changes \(R\) to \(-R\). Its limits at \(O,T^\sharp\) are \(1,-1\).

Both lifts \(S,S+T^\sharp\) of \(T_3\) are order two (\(v=0,\ u=7\pm4\sqrt3\)). Since \(x(T_3-B)=3(x(B)+1)/(x(B)-3)\), one has \(f_0(T_3-B)f_0(B)=4/3\). For each lift \(S\) this implies
\[
 R(S-A)R(A)=R(S),\qquad R(S)^2=4/3.\tag{2}
\]
Indeed the square of the left side is the nonzero constant \(4/3\), so the function is constant over the algebraic closure and evaluation at \(A=O\) fixes its exact value. This holds also in characteristic \(p>3\) by the same calculation on the good models. On the preimage of the base unit locus the function \(R\) is regular and invertible: a function and its inverse integral over a normal local ring belong to it. Thus the formulas allow removable denominators.

## 3. Galois descent and the ramified residue comparison

For each CM index choose any lift \(A_{\mathfrak a}\) of \(\phi(x_{\mathfrak a})\) to \(E^\sharp\). Set
\[
 A=\sum A_{\mathfrak a},\qquad C=\prod_{\mathfrak a}R(A_{\mathfrak a}),\qquad
 F=\prod_{\mathfrak a}f(x_{\mathfrak a})=C^2 .
\]
The points \(x_{\mathfrak a}\) are not cusps. Since \(P\in2E_0(K)\), its two lifts under \(\widehat\psi\) are \(K\)-rational: use \(\psi\) of a rational half over \(K\), and translate by the rational kernel for the second lift. In particular \(A\in E^\sharp(K)\). For every \(\sigma\in G_K\), comparison of \(\sigma A_{\mathfrak a}\) with the chosen lifts of the permuted indices changes some lifts by \(T^\sharp\). There are an even number of changes since the sum \(A\) is fixed. Thus the product of signs is \(+1\), and \(C\in K^\times\). Independent initial lift choices can change \(A\) by the kernel and \(C\) by its corresponding sign, with no other ambiguity.

Complex conjugation of the full orbit on \(X_0(48)\) is its image under \(w_{48}\) as a multiset. Therefore \(F\overline F=(4/3)^h\). The square root \(C\overline C\) is positive in the complex embedding, so \(U=C/(4/3)^{h/4}\) has norm 1. For \(p\mid n,\ p\ne17\), §4 shows \(f(x_{\mathfrak a})\) is a unit, allowing reduction of all \(R(A_{\mathfrak a})\) at a place containing the lifts. Each inertia pair has lift sum reducing to \(S+\epsilon T^\sharp\), \(\epsilon\in\{0,1\}\). By (2) its product is \((-1)^\epsilon R(S)\), with the same lift \(S\) chosen as reference for all pairs at that place. Since \(h/2\) is even and \(2S=O\), summing and multiplying give
\[
 \widetilde A=(\sum\epsilon)T^\sharp,\qquad
 C\bmod p=(4/3)^{h/4} R(\widetilde A),\qquad
 U\bmod p=R(A)\bmod p .
\]
The tilde denotes reduction, not conjugation. For the nonzero branch, \(R(A)^2=f_0(P)=(x_D-n)/x_D\), so \(R(A)=\pm\rho_Q\) in \(\mathbf Q\), one global sign.

## 4. CM differential calculation of the exact ideal

Work at a place over \(p\), normalize \(v(p)=1\), and extend locally to good models of the CM elliptic curves (their \(j\)-invariants are integral). For each order-\(d\) subgroup of the cyclic level kernel write \(\nu_d:E_1\to E_d\) for the quotient, \(\nu_d^*\omega_d=h_d\omega_1\) for good invariant differentials. Analytically use \(E_1=\mathbf C/(\mathbf Z+\tau\mathbf Z)\), with level generated by \(1/48\). The quotient lattice \((1/d)\mathbf Z+\tau\mathbf Z\), scaled by \(d\), gives \(E_d=\mathbf C/(\mathbf Z+d\tau\mathbf Z)\); the analytic quotient map is \(z\mapsto dz\). If \(\omega_d=c_d\,dz\), then \(c_d/c_1=h_d/d\). The analytic discriminant \(\Delta(d\tau)=\eta(d\tau)^{24}\) is a common period-normalization constant times \(c_d^{12}\Delta(E_d,\omega_d)\). The common constant and the factor from \(c_1\) cancel since \(\sum r_d=0\). The resulting algebraic identity and valuation are
\[
 f^{24}=\prod_d\left((h_d/d)^{12}\Delta(E_d,\omega_d)\right)^{r_d},
 \qquad v(f)=\frac12\sum_d r_d\bigl(v(h_d)-v(d)\bigr).\tag{3}
\]
Good discriminants are units. This derivation uses 24th powers only and introduces no root-of-unity factor.

For \(p>3\) the isogenies are prime to \(p\), so \(v(f)=0\). At \(p=2,3\) the primes split in \(K\). The two CM idempotents of \(O_K\otimes\mathbf Z_p\) cut out height-one factors of the good \(p\)-divisible group; the idempotent acting on the tangent line is connected, and the other is étale. The CM tangent action is the same at a given place for the entire class orbit, because all pairs have the same CM type and the class action fixes \(K\). For multiplication by \(\alpha\in O_K\) it is the residue embedding of the analytic action \(\alpha\) on \(dz\). Thus, with this choice of CM embedding, the level \(\mathfrak p_p\)-kernel is connected at the place \(\mathfrak p_p\), and étale at its conjugate. Equivalently the places can simply be named by which one makes the chosen level arm connected. Every smaller \(p\)-primary level subgroup in (3) is on that same arm.

In the étale case \(v(h_d)=0\); in the connected case its dual has unit differential, so \(\widehat\nu_d\nu_d=[d]\) gives \(v(h_d)=v_p(d)\). The prime-to-\(p\) factors are units in either case. With the exact sums \(\sum r_d v_2(d)=-4,\ \sum r_d v_3(d)=2\), the connected valuation of \(f\) is zero at both primes, while the étale valuations are 2 and \(-1\) respectively. Summing over the whole orbit, halving for \(C^2=F\), and dividing by the rational normalizer gives
\[
 (U)=
 \left(\frac{\overline{\mathfrak p}_2}{\mathfrak p_2}\right)^{h/2}
 \left(\frac{\mathfrak p_3}{\overline{\mathfrak p}_3}\right)^{h/4},\tag{4}
\]
with \(\mathfrak p_p\) naming the connected place. No assumed good reduction of \(X_0(48)\) at 2 or 3 is used.

## 5. The common sign and fourth divisibility

The ramified ideals at 17 and any two genuine distinct primes of \(\beta\) generate \(C_2^3\) in the class group. Each of the seven nontrivial products has positive nonsquare norm \(m<n/4\) since \(n\) includes other genuine odd primes. Such an integral ideal cannot be principal: a rational integer generator would give square norm, and a nonrational integer of \(K\) has norm at least \(n/4\) from \((a^2+nb^2)/4\). For any class \(c\), the cyclic group \(\langle c\rangle\) meets this elementary 2-subgroup in at most two elements. Its index is therefore divisible by four, so \(h/4\) kills every class.

Consequently the ideal \(\mathfrak a=\overline{\mathfrak p}_2^{h/2}\mathfrak p_3^{h/4}\) has a generator \(\alpha\) which is a unit at every odd ramified prime. Equation (4) gives \(U/(\alpha/\bar\alpha)\in O_K^\times=\{\pm1\}\). Since conjugation acts trivially on the residue field at a ramified prime, \(\alpha/\bar\alpha\) reduces to 1. Hence \(U\) has the same sign at all \(p\mid n,\ p\ne17\); we do not need or claim its choice-dependent absolute sign.

If \(P_D\ne O\), the two coherent root signs in §1 agree, so the first half \(Q\) has Kummer class in the torsion image. Subtract the corresponding rational 2-torsion point \(T\) to get \(Q-T=2B\). Doubling kills \(T\), giving \(P_D=2Q=4B\) exactly. The result holds for \(P_D=O\) without a half-coordinate formula. This supplies neither a second marked half nor nonvanishing of the order-three phase; multiplication by four remains invertible on that receiver.

### Exact dependencies and replay

- *The raw level-48 Heegner trace is a rational double*, paper SHA-256 **59feb8a9913e701fb1c82116c15908858712899c0bc53dfc603e100db36ea430**, supplies the freely paired inertia indices off 17, the formal local valuations and the selected Selmer decomposition.
- *A fixed-level finite Heegner certificate for the actual balanced detector pair*, paper SHA-256 **f1ffe375bf6fe92afe707d06f88dfc6bef2bb2da80532f48cc939f65e395104c**, supplies the literal \(\phi,w_{48}\) and signed trace.
- *A shared final prime retains the two Selmer eights under a detector split*, paper SHA-256 **4b2d39bf6b4f5e9dda8e33482c723dfba02569f8a0e285c005c646aa35d5fe6e**, supplies the exact original selector, eight and mark.

The replay checks the modular-unit exponents and orders at all cusp denominators, oriented lift signs and finite controls for the coherent half calculation. It evaluates no CM point, class group, or Heegner trace.

    python3 -B replay_level48_first_half.py | cmp - EXACT-LEVEL48-FIRST-HALF.json
    sha256sum -c SHA256SUMS
