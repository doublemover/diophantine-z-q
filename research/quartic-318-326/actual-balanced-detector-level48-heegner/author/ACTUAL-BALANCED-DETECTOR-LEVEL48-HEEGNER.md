# A fixed-level finite Heegner certificate for the actual balanced detector pair

Fix **one** original detector pole \(b\) (190, 241 or 292) and its literal positive \(\beta=[17b]\), \(\theta=[1-b/17]\). Fix a selected balanced pair \(n_1,n_2\) from the exact two-eights construction. There is no change to \(b\), its preparation index, the mark, or the relative twist class. The following gives a finite, positive-only arithmetic test on the **same** curves, at modular level 48, and the exact remaining input. No numerical detector, verified nonzero trace, or rational point on an original detector is supplied here.

## 1. A single nontorsion point on each selected curve is enough

Write \(E_n:y^2=x(x-n)(x+3n)\). The selected curves have rational full \(2\)-torsion and their exact \(2\)-Selmer dimension is three, with the specified class \((\beta,1)\) in the ordered coordinates \((x+3n,x-n)\). Their rational torsion is exactly \(C_2^2\): at any \(p\mid\beta\), \(p\ge5\), the base level-48 curve has good reduction and its quadratic twisting character ramifies there. For every auxiliary prime \(s\ne p\), an inertia element consequently acts as \(-1\) on the whole \(s\)-primary torsion. There are at least two distinct such \(p\). Thus there is no odd rational torsion and the rational \(2\)-primary group is killed by 2.

For clarity the four torsion classes in these ordered coordinates are
\[
 (1,1),\quad (3n,-n),\quad (n,1),\quad (3,-n).
\]
They follow from the specialized root coordinates of the full Kummer map. The second coordinate of the mark is 1, and \(\beta\ne1,n\bmod\mathbb Q^{\times2}\), since \(n\) is squarefree and includes the fresh \(q_0\nmid\beta\). Thus the mark is not a torsion class.

If \(E_n(\mathbb Q)\) has a nontorsion point, then the injection \(E_n(\mathbb Q)/2E_n(\mathbb Q)\hookrightarrow\mathrm{Sel}_2(E_n)\) is an isomorphism: the source dimension is at least \(1+2\) and the target dimension is exactly three. In particular the rank is exactly one, the literal mark is rational, and an actual representative of the mark is not a torsion point. No assertion about the divisibility by 2 of the nontorsion witness itself is needed. Parity at 2 alone would not justify this step: rank zero and a single divisible \(2\)-primary Sha direction would have the same odd \(2^\infty\)-corank.

To return to the exact source equations put \(B=17b\), \(\delta=1-b/17\). Choose rational points of the marked class on the two actual curves, with abscissas \(x_i=B r_i^2\). Choose \(\eta\in\mathbb Q^\times\) with \(n_2/n_1=B^2\delta\eta^2\), possible since the ratio has class \(\theta\). Divide the coordinates of the first point by \(r_1^2,r_1^3\); divide the second by \((r_1\eta)^2,(r_1\eta)^3\). Then the parameters are \(T=n_1/r_1^2\) and \(TB^2\delta\); the abscissas are \(B\) and \(Bs^2\), with \(s=r_2/(r_1\eta)\ne0\). These are the literal \(\mathsf{NormalizedPolePoints318.PointPair}(b)\) equations. The direct degree-two graph route is a separate sufficient certificate for those same equations; the present argument makes no claim on the rank or Selmer group of its auxiliary Jacobian.

## 2. An unweighted trace at level 48, with the exact sign

The original \(q_0\) CRT admits the refinement \(q_0\equiv7\bmod24\). The helpers are \(1\bmod24\), \(\beta\equiv17\bmod24\) and each side, including any shared repair, contributes \(1\bmod24\). Thus we may choose both \(n_i\equiv23\bmod24\). This is a restriction on selection, not an assertion about every previously fixed \(q_0\). For \(D=-n_i\), \(D\) is a negative odd fundamental discriminant and \(D\equiv1\bmod24\), so 2 and 3 split in \(K=\mathbb Q(\sqrt D)\). This is the Heegner condition for **48**, not for \(48n_i^2\).

Use the explicit \(X_0(48)\) model \(Y^2=X^8+14X^4+1\) from [Colò, Appendix A, pp. 247–248](https://www.leonardocolo.com/documents/thesis/PhD_Thesis.pdf). On its smooth completion, a degree-two morphism to the literal \(E_0=E_{-1}:y^2=x(x+1)(x-3)\) is
\[
 t=X-1/X,\qquad w=Y/X^2,\qquad
 \phi(X,Y)=\left(x=\frac{w+t^2+2}{2},\ y=tx\right).
\]
Indeed \(w^2=t^4+4t^2+16\) and \(xt^2=(x+1)(x-3)\); for generic \((x,y)\), \(t=y/x\), \(w=2x-t^2-2\), and \(X\) satisfies \(X^2-tX-1=0\). The involution \((X,Y)\mapsto(-1/X,Y/X^4)\) fixes \((t,w)\), so the degree is exactly two. This is the map under the published modular identification of the model, not a morphism from a newly chosen genus-three curve. On \(X=0\) and at infinity the \(+\) branch (\(Y=1\) or leading \(Y/X^4=1\), respectively) maps to \(O\); the other branch maps to \((0,0)\). These values follow by expansion on the actual smooth curve. They also define direct finite-field evaluation at its exceptional chart points.

In Colò's long coordinates use \(y_{48}=(Y+X^4+1)/2\) in the printed formula for \(w_{48}\). Substituting and reducing \(Y^2=X^8+14X^4+1\) gives the sign \(+4\), so
\[
 w_{48}(X,Y)=\left(\frac{X+1}{X-1},\frac{4Y}{(X-1)^4}\right).
\]
It sends \((t,w)\) to \((4/t,4w/t^2)\). The resulting \(E_0\) coordinates are \(x'=3(x+1)/(x-3)\), \(y'=12y/(x-3)^2\), the chord formulas for \((3,0)-(x,y)\). Therefore, **as morphisms**,
\[
                    \phi\circ w_{48}=T_3-\phi,\qquad T_3=(3,0).
\tag{1}
\]
The shape of this exact signed identity does not require an analytic normalization of \(\phi\).

Choose a level ideal \(\mathfrak n=\mathfrak p_2^4\mathfrak p_3\) with one prime over each split prime; then \(O_K/\mathfrak n\) is cyclic of order 48. For each ideal class \([\mathfrak a]\) take the oriented CM pair \((\mathbb C/\mathfrak a,\mathbb C/\mathfrak a\mathfrak n^{-1})\) with the actual cyclic quotient isogeny. By the [classical CM construction of Gross–Zagier, §I.3](https://wstein.org/papers/bib/Gross-Zagier_Heegner_points_and_derivatives_of_Lseries.pdf), these points are defined over the Hilbert class field \(H\), and the same-orientation class orbit is the full orbit over \(K\). Let \(P\) be the sum of their \(\phi\)-values, in \(E_0(K)\). Changing the seed class only permutes summands. Complex conjugation changes \((\mathfrak a,\mathfrak n)\) to \((\bar{\mathfrak a},\bar{\mathfrak n})\); \(w_{48}\) reverses the quotient and sends \([\mathfrak a]\) to \([\mathfrak a\mathfrak n^{-1}]\) in exactly that opposite orientation, since \(\mathfrak n\bar{\mathfrak n}=(48)\). Thus the two operations agree on the full **multiset**, and (1) gives
\[
 cP=h(D)T_3-P,\qquad S=P-cP=2P-h(D)T_3,\qquad [2]S=[4]P.       \tag{2}
\]
There is no identification of a single arbitrary conjugate with \(w_{48}\) without its class-index permutation. Here \(h(D)=|\mathrm{Pic}(O_K)|\).

The point \(S\) is exactly anti-invariant under \(c\), and descends to the required twist \(E_n\): on affine points the descent is \((x,y)\mapsto(Dx,D\sqrt D\,y)\). Replacing \(\phi\) by \(\phi+C\) for any rational constant keeps \(S\) unchanged since the trace changes by \(h(D)C\). For the raw map above the shortcut \([4]P\) is exactly valid; under a general translated map, first subtract the corresponding \(h(D)C\) or use \([2]S\) directly. In particular either normalization at the actual infinity branches leaves \([4]P\) unchanged, since those constants are killed by 2.

## 3. One common finite reduction test and its data

Choose a good prime \(\ell\ge5\), not dividing \(n_1n_2\). For each \(D_i\), reduce the correctly oriented **whole** class orbit at one common place over \(\ell\) in its own class field (a choice for each field, with all its summands evaluated at that choice). Collisions of reduced coordinates retain multiplicity. Let \(\bar P_i\) be the finite-field sum obtained using the fixed \(\phi\) above. The check is
\[
                         [4]\bar P_1\ne O \quad\text{and}\quad
                         [4]\bar P_2\ne O .                   \tag{3}
\]
By good reduction and (2) this implies \([2]S_i\ne O\) globally. Since the descended rational torsion is killed by 2, both descents are nontorsion points. Section 1 then proves the marked \(\mathsf{PointPair}(b)\). There is no Kolyvagin nonvanishing assumption in the soundness of (3). Failure of a reduction check says nothing about rank or even about the global Heegner trace.

The same explicit small prime 29 is usable whenever \(29\nmid n_1n_2\). The base \(E_0\) has 24 points over \(\mathbb F_{29}\), and its nonsquare twist has 36. In a split arm the reduced \(P_i\) lies in \(E_0(\mathbb F_{29})\); in an inert arm \([4]\bar P_i\) lies in the Frobenius-minus group inside \(E_0(\mathbb F_{29^2})\), of order 36. Neither case forces (3) to vanish by torsion exponent; there is no need for 29 to have the same splitting type in both arms. At a split prime actual CM summands may be in a larger field: the residual extension degree in \(H_i/K_i\) is the order of the prime ideal class. They sum in the stated base group.

There is always a common prime **inert in both** \(K_i\) whose residual minus group has odd torsion. Indeed choose by Chebotarev the class of complex conjugation in the compositum \(K_1K_2\mathbb Q(E_0[5])\), outside the finitely many forbidden primes. Conjugation is nontrivial on both imaginary fields and has a \(-1\) eigenline on \(E_0[5]\) (its eigenvalues are \(1,-1\) by its order and determinant). At each such inert \(\ell\), the prime ideal \((\ell)\) of \(K_i\) is principal and therefore splits completely in \(H_i/K_i\). **All modular CM summands themselves** reduce in \(\mathbb F_{\ell^2}\) in both arms. This does not guarantee nonzero traces.

A proof-producing CM input can certify one oriented reduction seed per arm. For an inert prime, an elliptic curve over the finite algebraic closure with an explicit embedding \(O_{D_i}\hookrightarrow\operatorname{End}(A)\) suffices; equivalently certify one noninteger endomorphism with the minimal polynomial of \((1+\sqrt{D_i})/2\). The order is maximal and the embedding is optimal. The classical Deuring lift of that pair gives a characteristic-zero CM seed; only the unramified moduli points, not necessarily every auxiliary coordinate of the oriented curve or endomorphism, are asserted rational over \(\mathbb F_{\ell^2}\). See [Deuring's theorem and oriented curves in Voight](https://link.springer.com/chapter/10.1007/978-3-030-56694-4_42) and [Colò–Kohel's ideal action](https://arxiv.org/abs/2012.10803). Starting from the lift, prime-to-\(48\ell\) representatives of all ideal classes act by their common endomorphism kernels, with the same chosen \(\mathfrak n\)-subgroup transported. Reduction commutes with those finite étale kernels and quotients. Thus computing the action on the oriented finite-field seed gives precisely a reduced oriented orbit, rather than a list of unlabelled supersingular \(j\)-invariants. A checker can alternatively accept reductions certified from exact characteristic-zero CM data. The input must identify the actual cyclic subgroup in the model of \(X_0(48)\); in the supersingular case the two \(j\)-values alone do not certify a branch.

Direct evaluation uses \(h(D_1)+h(D_2)\) CM-pair evaluations and corresponding elliptic additions. Binary quadratic forms give exact enumerations of those class sets and prime-to-\(48\ell\) ideal representatives. Finding an oriented seed and verifying subgroup-to-model coordinates are separate costs; no complexity bound for their production is claimed. This removes the large modular level \(48n_i^2\) and, in the jointly inert strategy, any growing residue field degree for the moduli points. It does not make \(h(D_i)\) small or evaluate (3). A balanced split can shrink the larger of \(|D_1|,|D_2|\) at fixed common factor. No actual original detector input and complete selected primes have been numerically supplied here.

## 4. Comparison with the smallest analytic inputs

At \(E_0\)'s conductor 48 the base central value is already strictly positive, without a new arithmetic hypothesis. The positive-sign Mellin formula at the central point is \(2\sum_{m\ge1}a_m r^m/m\), with \(r=e^{-2\pi/\sqrt{48}}<1/2\), \(a_1=1\) and \(a_2=0\). The elementary bound \(|a_m|\le d(m)\sqrt m\le2m\) makes the \(m\ge3\) absolute tail at most \(2r^3/(1-r)<r\), before the common factor 2. The positive sign for \(E_0\) is the exact base sign used in the published detector selection. Gross–Zagier therefore says the characteristic-zero trace \(P_i\) is nontorsion exactly when \(L'(E_{n_i},1)\ne0\), since the base-change \(L\)-function is \(L(E_0)L(E_{n_i})\). That equality is explanation of the global test, not an extra prerequisite for the implication (3).

A different sufficient finite input is a **certified bound** \(\dim_{\mathbb F_p}\mathrm{Sel}_p(E_{n_i})\le2\) for each arm at a good ordinary irreducible prime \(p>2\). Both signs are negative; the [Dokchitser–Dokchitser parity theorem, Thm. 4.19](https://arxiv.org/pdf/math/0610290) makes the \(p^\infty\)-Selmer corank odd. The finite \(p\)-Selmer bound makes it at most two (here \(E_{n_i}(\mathbb Q)[p]=0\)), hence exactly one. [Yan–Zhu, v4 Thm. 5.11](https://arxiv.org/pdf/2412.20078v4) then gives rank one. No integral main conjecture or BSD formula is needed. For an actual selected pair a common \(p\equiv5,13,17\bmod28\) avoiding \(n_1n_2\) suffices, including \(p=5\) when good. In fact \(p\equiv1\bmod4\) and the good reduction has rational full \(2\)-torsion, so its trace is \(2\bmod4\), nonzero with \(|a_p|<p\). The characteristic polynomial of base Frobenius at 7 has trace zero and discriminant \(-28\), nonsquare modulo every such \(p\); this proves irreducibility, unchanged by twisting. The bound on the actual odd Selmer groups, or the established alternative of a nonzero normalized cyclotomic digit on each arm, still has to be certified. Neither follows from the two selected Selmer eights.

## Exact pins and replay

- *Balanced Actual Detector Selmer Eights*, paper SHA-256 `4b2d39bf6b4f5e9dda8e33482c723dfba02569f8a0e285c005c646aa35d5fe6e`, for the literal profiles, the possible shared \(q_0\) refinement, and the hypotheses at the selected marks.
- `NormalizedPolePoints318.lean`, SHA-256 `410995ba113f37dfcb54261e61eb6b90fde58242a4fa0eed79282e99ad060542`.
- The fixed-level control checks all chart points over \(\mathbb F_{29^2}\), the sign relation, the target field orders and base traces; it does **not** supply CM labels, actual reductions or a selected numeric detector.

    python3 -B replay_level48.py | cmp - EXACT-LEVEL48-CONTROLS.json
    sha256sum -c SHA256SUMS
