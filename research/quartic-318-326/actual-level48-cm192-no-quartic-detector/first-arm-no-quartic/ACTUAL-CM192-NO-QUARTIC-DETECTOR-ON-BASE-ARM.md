# No quartic class character can detect the base arm's marked sign

For the genuine first arm of the original balanced pair with \(u=1,\ v=\theta\), the marked relative ideal class is a nonzero element of order two which belongs to **\(4\,\mathrm{Cl}(L)\)**. Hence not only quadratic but also quartic unramified characters fail to distinguish its two possible sign-ideal classes. The extra divisibility follows from the literal balanced Selmer matrix, not from predicting any class-group distribution. No selected rank or signed CM ideal is evaluated.

## 1. The same norm-solution can use a rational denominator

Keep \(D=-n\), \(K=\mathbf Q(\sqrt D)\), \(F=\mathbf Q(\sqrt3,\sqrt{17})\), \(L=F(\sqrt D)\), \(\beta=17B_*\), and \(\mathfrak B\) from the prior relative receiver. At every odd \(p\mid n\) the four rational 2-torsion classes account for all local Kummer classes and have distinct valuation pairs. Exact local presence of \((\beta,1)\) thus gives:
- If \(p\mid\beta\), the mark equals \((n,1)\), so \(n/\beta\) is a square unit in \(\mathbf Q_p\).
- If \(p\nmid\beta\), the mark is trivial locally, so \(\beta\) is a square unit.

In particular \(\beta\) itself is a norm from **\(K/\mathbf Q\)**. For each \(p\mid\beta\), \(\beta/(-D)=\beta/n\) is a square unit; multiply the norm of \(\sqrt D\) by a rational local square. This includes 17. At \(p\mid n,\ p\nmid\beta\) use the local square. At 2 and 3, \(D\equiv1\bmod24\) gives local splitting. At every other finite place the extension is split or unramified and the target is a unit; at the real place \(\beta>0\). The quadratic Hasse norm theorem therefore gives
\[
 a,b\in\mathbf Q,\qquad a^2-Db^2=\beta.
\]
The element \(\alpha_B=(a+b\sqrt D)/\sqrt{17}\) then has norm \(B_*\) over \(F\) and is a valid input to the preceding square-root construction \([\mathfrak c_B]^2=[\mathfrak B]\).

Importantly the denominator of its trace \(s=2a/\sqrt{17}\) over \(F\) is the extension of a positive **rational** integer \(d\): away from 17 the factor \(\sqrt{17}\) is a unit; at 17, \(a+b\sqrt D\) has local ramified order one since its norm \(\beta\) has valuation one. Therefore \(2a\) is divisible by 17 (the rational trace reduces to zero in the ramified residue field), and \(2a/\sqrt{17}\) is integral there. Thus one can use the positive denominator of \(2a\) as \(d\), with no factor at 17; if \(2a=0\), use \(d=1\). In addition \(d\) is a unit at every relative ramifier, by the preceding trace-denominator proof. Consequently the quadratic character expression for \(\mathfrak c_B\) simplifies to
\[
 \chi_t(\mathfrak c_B)=
   \prod_{\wp\ \mathrm{relative\ ramified}}(t,d)_\wp
 = \prod_{\substack{p\mid n,\ p\ne17\\p\ \mathrm{split\ completely\ in}\ F}}
       \left(\frac d p\right)^{v_p(N_{F/\mathbf Q}(t))}.
 \tag{1}
\]
There are no archimedean factors since \(d>0\), and a rational unit is square in a degree-two finite residue field. At completely split primes the local Hilbert rows are residue signs of the rational unit \(d\) to the corresponding \(t\)-valuation powers, and their product uses the indicated rational norm exponent. Thus it suffices to show \(N_F(t)\) a rational square.

## 2. The sharp matrix excludes the only possible rational norm

Let \(\chi_t\) be any quadratic unramified class character of \(L\) which kills the relative ramified ideal classes. By the previous quadratic-genus theorem it descends from \(F(\sqrt t)\), and \(t\) has even valuations outside the relative ramified primes. At any relative ramified \(\wp\) the condition \(\chi_t=+1\) on its ideal is exactly that \(tD^{-v_\wp(t)}\) be square as a stripped unit modulo \(\wp\). If \(-1\) is a residue square at \(\wp\), this is also exactly the **norm** condition \(t\in N_{L_\mathfrak P/F_\wp}L_\mathfrak P^\times\): a ramified uniformizer \(\sqrt D\) has norm \(-D\), and a unit is a norm iff its residue is square. Elsewhere \(t\) is a norm at every finite place because its order is even and \(L/F\) is split or unramified.

In the actual first arm \(n=\beta q_0\prod I_j\), with \(\beta\) genuine primes \(1\bmod408\), all helpers \(1\bmod24\), and \(q_0\equiv7\bmod24\). At every relative ramifier except \(q_0\) the rational prime is \(1\bmod4\), hence \(-1\) is square already rationally. At \(q_0\), \((3/q_0)=-1\), so the residue field in \(F\) has degree two and again contains a square root of \(-1\). Therefore \(t\) is a norm at **all finite places** of \(F\). The same argument applies more generally under the condition that \(-1\) is a square in each relative ramified residue field, for example whenever all \(p\mid n,\ p\ne17\) split in \(\mathbf Q(\sqrt{-3})\): if such a \(p\) is \(3\bmod4\) then \(p\equiv7\bmod12\) and \((3/p)=-1\).

Let \(A\) be the signed squarefree representative of \(N_{F/\mathbf Q}(t)\). The compatibility of field norms in the étale local algebra square \(L=FK\) shows that \(A\) is a norm from \(K\) at every finite rational place: take the local norms \(t=N_{L/F}\alpha\), then use \(\mathrm N_{F/\mathbf Q}\mathrm N_{L/F}=\mathrm N_{K/\mathbf Q}\mathrm N_{L/K}\) on the products of completions. By Hilbert reciprocity it is also a norm at the real place and hence positive. Its supported bits are among prime divisors of \(n\), with **zero at 17 and \(q_0\)**: 17 is not relatively ramified; \(q_0\) has even residue degree in \(F\). Other primes need not be individually excluded.

Write \(x_p=v_p(A)\bmod2\) on the indexed rational support of \(n\). The local norm equations for \(A\) in \(K=\mathbf Q(\sqrt{-n})\) are the ordinary Laplacian equations \(L_0x=0\), where \(L_0\) denotes the original row-sum-zero binary matrix with off-diagonal \(pq\) entry the nonsquare bit of \((q/p)\). In detail at \(p\mid n\) the Hilbert-symbol formula says \((A/p)=+1\) when \(x_p=0\), and \(((n/A)/p)=+1\) when \(x_p=1\), after stripping both valuations; the minus from \(D=-n\) cancels the Hilbert symbol's double-depth sign. These are exactly the rows of \(L_0\).

The actual selected invertible matrix is the \(q_0\)-row and \(q_0\)-column deletion of
\[
 L_0+\lambda(e_{17}+e_{q_0})^{\mathsf T},
 \qquad \lambda_p=\text{nonsquare bit of }(3/p).
\]
It acts on \(x\) in the same way as \(L_0\), since \(x_{17}=x_{q_0}=0\). The \(q_0\) coordinate of \(x\) is zero, so invertibility of the exact deleted matrix forces \(x=0\). Both old three/four-helper cores are pinned in the exact companion-selection source; the finite control replays their full kernels. The proof uses the native invertibility, not an assumption that an arbitrary Selmer-marked twist has this particular matrix. Thus \(A=1\) and \(N_F(t)\) is a positive rational square.

## 3. Consequence

Equation (1) now gives \(\chi_t(\mathfrak c_B)=+1\) for every quadratic unramified character killing the relative ramified classes. In particular this includes every quadratic character that can be squared from an order-four character, since the ramified ideal classes have order dividing two. By the exact character-lifting criterion, no order-four character takes value \(-1\) on \([\mathfrak B]=[\mathfrak c_B]^2\). Because this class has order exactly two and is already invisible to quadratic characters, duality of the finite quotient \(\mathrm{Cl}(L)/4\mathrm{Cl}(L)\) gives
\[
 \boxed{[\mathfrak B]\in 4\,\mathrm{Cl}(L),\qquad [\mathfrak B]\ne 1.}
\]
In particular the group has an element of order at least eight. On the no-collision base arm the actual relative sign class is either \(1\) or \([\mathfrak B]\). Thus special Heegner intersection computations followed only by a quartic character would also be insufficient to distinguish that sign. A higher-order character need not automatically succeed. Arbitrary companion support may fail the relative residue-square condition above; no unconditional fourth-power statement for such support is made. No implication of rank zero or of nonexistence of the marked point is drawn.

### Exact dependencies and replay

- *Companion theta paired selection*, exact published paper **21c692023d5085335ff0ff4a31a943906acd27dc44549560fe63e2f86431fd9f**, §2 (actual matrix, correction, and both old cores), together with *A shared final prime retains the two Selmer eights under a detector split*, paper **4b2d39bf6b4f5e9dda8e33482c723dfba02569f8a0e285c005c646aa35d5fe6e** (exact \(u=1\) and actual local mark).
- *A conic-and-residue test for a quartic detector of the marked class*, paper **539f5fc2597fbc45b6596cdd9149d0fe6535367462689f1ecbcdc8193bf6a5d0**, identifies the square root ideal and the factorization-free character of its trace denominator.
- *Ordinary genus characters cannot see the marked relative ideal class*, paper **9ebfd5382aca7956109e91584026cf5a43444aaf2902d46e64c42c845c1341ef**, fixes all quadratic characters over \(F\) and the nonzero order-two class.

The replay works directly on the two retained exact matrix cores and checks that their kernels are zero. It computes no \(q_0\), norm-conic solution, CM value, or selected rank.

    python3 -B replay_base_sharp_kernel.py | cmp - EXACT-BASE-SHARP-NORM-KERNEL.json
    sha256sum -c SHA256SUMS
