# Independent cold review: one actual weighted detector component

**PASS**, exact paper and control bytes, 21 November 2026. Author paper
`96f6dd8f415a36c83eae7163e73ace7e17a76ae63ead1dcba1f59ddfe90b9940`,
author checksum list
`7af62937f312eeaac3014ab0583efb7e81acb7fa4e02414bc569427a8597e835`.
The complete control replay used the independently checked exact $D=-119$
CM pilot data
`8cfca028b915bd6c059853447faeb5c50bbee67f58ac4816e4b25f336bfcc85d`
and reproduced all 32,768 six-contact graphs and the signed finite
calibration bytes. No CM orbit for an actual selected detector was computed.

1. The first-arm graph can keep every old contact edge and replace the
   effective contact Laplacian by a tree through Schur complementation.
   The auxiliary pair's genuine row sums give the prescribed
   $\left(\begin{smallmatrix}0&1\\1&1\end{smallmatrix}\right)$ block,
   whose inverse has entry sum one. The separate helper produces the
   extra 17-edge after elimination, with the selected marked vector
   unchanged because the outside incidences are even. Removing 17
   recomputes the actual Laplacian on $s$; the single changing retained
   diagonal cancels the rank-one term in the 17 pivot. The first
   $q_0$-minor remains invertible. Appending $\theta$ retains the old
   block, uses final fixed diagonals and independent fresh-prime
   incidence bits, and still allows **one** shared prime by CRT.
   This reselects helpers/prime and uses the same fixed $(b,\beta,\theta)$,
   not a previously specified set of helper/final primes.
2. The primary [tiling-number paper](https://arxiv.org/pdf/2405.11132),
   Proposition 4.2(iii) and Theorem 2.7 give odd analytic $\mathcal L(s)$
   from this reduced determinant: $s\equiv7\bmod24$ uses the positive
   $+s$ formula, not the negative-twist divisor-sum formula.
   Theorem 2.8 and the explicit signed count give $\mathcal L(7)=1$;
   the same formula and integrality make $\mathcal L(s)$ an integer
   square. The Tamagawa factors at 2 and 3 and the period/torsion
   normalization yield the ratio with $4^{\omega(s)-1}$.
3. The genus character evaluates to $-1$ on the level ideal, so
   the sign $-\chi_{17}(\mathfrak n)=+1$ makes the weighted trace
   fixed by complex conjugation and anti-invariant over the real
   $\sqrt{17}$ component. Thus it descends to the **fixed**
   $E_{-17}$, not the moving $E_{17s}$.
   The signed $D=-119$ trace has nonzero fourfold reduction at 29,
   proving nontorsion for the reference on $E_{-17}$.
   [Cai–Shu–Tian, Theorem 1.1](https://arxiv.org/pdf/1408.1733#page=2)
   compares both raw weighted sums with the same map, $c=1$,
   no common level/discriminant prime, and the same quadratic-unit
   normalization. Its $1/\sqrt{|D|}$ factor yields the stated
   relative canonical-height formula. On the fixed rank-one component,
   the forced index shift is precisely $\omega(s)-1$ in two-adic
   valuation relative to the reference free coefficient.

No nonzero **unweighted** actual trace, primitive coefficient, rank statement,
or marked rational point is obtained for either moving target twist.
The finite control and analytic normalization do not bridge those character
components. This is a mathematical review, not a new Lean build.

Signed: independent arithmetic and evidence reviewer.
