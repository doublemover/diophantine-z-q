# One exact moving marked arc at the named p19 place

This bounded control uses \(D=-311,\ f=241,\ n=241\cdot311\) and the same \(\mathcal U\) as the complete p11 two-place evaluation. It constructs a true moving seed, its 19 horizontal 2-prime canonical models at 19 and **one** actual conductor-241 marked arc. Every factor on that arc is evaluated at all four real coefficient places. Its signed contribution to the named \(M_5\) projected exponent is zero, including modulo 13. This does not compute the full p19 exponent, reject the p19 prime, or give an original detector value. The separately unsupported calibration-diagonal branch is not used to choose this moving seed.

## Moving canonical seed and cycle

Work in \(\mathbf F_{19}(s)\), \(s^2=2\). On \(y^2=x^3-x\), use \(i:(x,y)\mapsto(-x,3sy)\) and 19-Frobenius \(\pi\). Here
\[
 V=8i+3\pi+2i\pi,\quad \alpha=(1+V)/2=-1+3i+3\eta+2i\eta,\quad
 \eta=(1+\pi)/2 .
\]
The norm of \(V\) is \(64+19(9+4)=311\), and its Lie value \(8(3s)=5s\) is the named \(\sqrt D\). The displayed \(\alpha\) is integral and optimal since \(D\) is fundamental. To realize \(\eta\), identify its \(\pi=-1\) cyclic 5-kernel, take the normalized Vélu quotient, and scale by 2 to the source. The code verifies the identity \([2]\eta=1+\pi\) as complete rational maps. It carries the degree-78 \(x\)-map of \(\alpha\) through 19 uniquely even-eigen 2-kernels by the exact quadratic rational-map descent of the frozen p11 cycle. No \(2^{19}\)-torsion is represented.

The cycle has length 19 by the same imaginary class number and nonprincipal even 2-prime. The principal generator \(\mu=(1341-31\sqrt D)/2\) chooses the closing scale by named differential \(1/u=\mu\); the direct residue map gives \((17,15)\) for \(u\) in the basis \(1,s\). The Hensel branch uses the normalized short model \(y^2=x^3-x+T\); its closure error at zero is \((171,0)\bmod19^2\), and the finite-difference derivative is \((14,6)\bmod19\), a unit. The rigorous identification of the canonical lift is the same simple-branch argument as at 11: the actual optimal CM branch must close by this principal ideal and named isomorphism, and this is the unique closing root in the short-model disc. The table has \(T=(8910294682,1166826974)\bmod19^8\), together with all 19 normalized kernel lifts. The replay recomputes the branch and checks the closure exactly.

## One true marked arc and its factor depths

Use named \(\sqrt{241}=4s,\ \sqrt{-n}=2\), and the ordered eigenvalues \(2,0\) on the 16/3 lines. The even 16-root and the zero 3-root are obtained by projecting exact finite torsion with \(\alpha-15\) and \(\alpha-1\), respectively; verify exact orders and eigenvalues. Take just one deterministic, nonzero order-241 seed point. The first primitive 241 lift and both level marks are constructed by the same checked unit-derivative conditions as the p11 complete-two-arc proof. The finite step cross-checks the direct quaternion formula for \(V\) with \(2\alpha-1\), and Miller's pairing has the named positive Gauss sum \(+4s\), so this arc has \(\chi=+1\).

In the unramified extension of degree 96, take the actual degree-241 Vélu quotient and transport both tame marks. The degree-96 field suffices since \((-19)^{48}=1\bmod241\), and 16 and 3 also divide the order of the relevant formal scalar on that torsion. Both ordered quotient charts identify the actual \(X,Y\), which descend to basis \(1,s\):
\[
 X=(8051806863,7603945419),\qquad
 Y=(9864930482,10767954497)\pmod{19^8}.
\]
The coefficients in the checked full curve equation and both distinct \(t_{16}\) identities use this actual lift, not just its residual \(j\).

The fixed real field has four choices \((\sqrt5,\sqrt6)=(\pm9,\pm5)\) over this named \(\sqrt{-n}=2\) root. Lift \(A=8,\ i=3s,\sqrt2=s,\sqrt3=12s\), then use \(A\mapsto i/A\) and \(\sqrt3\mapsto-\sqrt3\) independently to obtain these four coefficient places. Both real radicals and \(-n\) are squares at 19, so all relative ideal norm residue weights here are one. All 160 fixed factors on **each** of these four embeddings are resolved, with maximum depth one and the complete raw \(\mathcal U\) valuation zero. The binary prime of interest has \(\sqrt{-5n}=9\cdot2=-1\bmod19\). Its signed one-arc contribution is the \(\chi\)-weighted sum at \(\sqrt5=+9\) minus the corresponding two values at \(\sqrt5=-9\), using the global complex-conjugate inversion at the opposite moving root. This gives \(0\bmod13\), which cannot meet any 13-primary obligation by itself. The other 4,597 arcs are not evaluated and may contribute.

Replay both files with Python 3 and python-flint 0.9.0 from the exact donor-relative layout:

~~~sh
sha256sum -c SHA256SUMS
python3 -B check_D311_p19_cycle.py | cmp - EXACT-D311-P19-CANONICAL-2-CYCLE.json
python3 -B check_D311_p19_one_arc.py | cmp - EXACT-D311-P19-ONE-MARKED-ARC.json
~~~
