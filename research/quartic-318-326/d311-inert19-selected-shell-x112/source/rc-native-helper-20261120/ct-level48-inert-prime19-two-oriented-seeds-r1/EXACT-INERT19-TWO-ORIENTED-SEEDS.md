# The two explicit normalized supersingular sources at the inert prime 19

This is a finite source certificate for either selected detector arm if its fundamental \(D=-n\equiv1\bmod24\) is inert at 19. It supplies both supersingular source orders and the exact orientation equations, not a computed original trace.

## 1. Both supersingular classes, with concrete endomorphisms

The Hasse coefficient of \(x^{18}\) in \((x^3+Ax+B)^9\) is \(10A^3B+8B^3\) modulo 19. Thus the two supersingular classes are \(j=1728\) and \(j=7\), using \(B=0\) or \(B^2=13A^3\), respectively. Both models below have 20 points over \(\mathbb F_{19}\) and 400 over \(F=\mathbb F_{19}[\sqrt2]\), with Frobenius \(\pi^2=[-19]\).

For \(j=1728\) take \(A_{1728}:y^2=x^3-x\), \(i(x,y)=(-x,3\sqrt2\,y)\). Then \(i^2=-1\), \(\pi i=-i\pi\), and \(\eta=(1+\pi)/2\) is integral since all \(2\)-torsion is rational over \(\mathbb F_{19}\). The full geometric order has basis \((1,i,\eta,i\eta)\), by the same trace-pairing discriminant argument as the prime-7 source: the determinant in the basis \((1,i,\pi,i\pi)\) has absolute value \(16\cdot19^2\), and the change of basis has determinant \(1/4\). The degree of \(\eta\) is five; its kernel is the Frobenius-minus order-five subgroup, since 2 is invertible on \(5\)-torsion. Its four nonzero points are
\[
              (13,\pm3\sqrt2),\qquad (14,\pm4\sqrt2).
\]
The exact normalized Vélu quotient is \(y^2=x^3+13x\) and the scaling back to \(A_{1728}\) is \((x,y)\mapsto(2^2x,2^3y)\). Its tangent factor \(1/2\) uniquely identifies it with \(\eta\); the replay also checks the formula on all \(F\)-points.

For \(j=7\) take \(A_7:y^2=x^3-x+5\). The norm-two endomorphism \(\eta\) is the normalized Vélu quotient at \((11+3\sqrt2,0)\) followed by scaling of weight two and three by \(u=5+13\sqrt2\). The exact morphism identities are \(\eta^2-\eta+[2]=0\) and \(\pi\eta+\eta\pi=\pi\); their differences vanish on all 400 points of \(A_7(F)\), and have degree bounds \((2+\sqrt2+2)^2<400\) and \((2\sqrt{38}+\sqrt{19})^2<400\). A nonzero endomorphism could not have this many distinct points in its kernel. With \(\alpha=2\eta-1\), \(\alpha^2=-7\) and \(\alpha\pi=-\pi\alpha\). The order with basis \((1,\eta,\pi,\eta\pi)\) has reduced discriminant \(7\cdot19\).

For the necessary index-seven enlargement, use \(F[T]/(T^3-4)\); the base element \(4\) has order nine, so a root has order 27 and \(361\) has order three modulo 27. This is a field and \(A_7\) over it is \(A_7[19^3+1]\). The replay checks an independent full \(7\)-torsion basis, computes all four endomorphism matrices, and finds the exact numerator
\[
               1+5\eta+5\pi+4\eta\pi
\]
kills \(A_7[7]\). Thus division by the separable \([7]\) gives an actual integral endomorphism \(\nu\). Its augmentation enlarges the lattice by index seven, so the full order is \((\nu,\eta,\pi,\eta\pi)\). At the required \(48\)-torsion one may evaluate \(\nu(P)\) by applying that numerator to \([7]P\).

## 2. The two representation sums use one tangent branch

For \(A_{1728}\) the trace-one embedding generator has the form
\[
 \omega=\frac{1+r i+c\pi+d i\pi}{2},\qquad
       n=r^2+19c^2+19d^2,\quad c\text{ odd},\ r\equiv d\bmod2 .
\]
Conjugation by \(i\) sends \((r,c,d)\mapsto(r,-c,-d)\), so choose \(c>0\), exactly one representative. For \(A_7\) write
\[
 \omega=x\nu+(1-x)\eta+z\pi+w\eta\pi.
\]
The coefficients of \(2\omega-1\) on \((\alpha,\pi,\alpha\pi)\) are \((A_1/7,C_1,B_1/7)\), with \(A_1=7-2x,\ B_1=4x+7w,\ C_1=2x+2z+w\). Hence
\[
                   7n=A_1^2+19B_1^2+133C_1^2
\]
with \(A_1\) odd, \(2A_1+B_1\equiv0\bmod7\), and \(C_1\equiv (2A_1+B_1)/7-2\bmod2\). These invert the integer change of variables. The only units of \(A_7\) are \(\pm1\), and no sign division is made there after normalization.

**The tangent normalizations cannot be picked separately.** Fix one residue value for \(\sqrt D\). On \(A_7\), \(d\alpha=2/u-1=5\sqrt2\), whereas on \(A_{1728}\), \(di=3\sqrt2\). So if \(A_1/7\equiv s_0\bmod19\) with \(7s_0^2\equiv n\), require \(r\equiv 5s_0/3\bmod19\) on the other source. Then both differentials equal the same \(5s_0\sqrt2\). The [normalized Deuring correspondence](https://people.math.wisc.edu/~tonghaiyang/deuring.pdf), §3, makes the union of these two sets the full normalized class orbit. Attaching the fixed level ideal requires the same selected eigenkernels at 16 and 3, just as at 13. No arbitrary union of opposite tangent branches is involved.

For the two toy discriminants, the normalized representation counts are:

| \(D\) | \(s_0\) | coherent \(r\bmod19\) | \(j=7\) | \(j=1728\) | independent \(h(D)\) |
|---|---:|---:|---:|---:|---:|
| \(-47\) | 2 | 16 | 3 | 2 | 5 |
| \(-119\) | 6 | 10 | 7 | 3 | 10 |

They validate inputs to the local trace, **not** finite trace values at 19. The fixed level-48 point lookup is a separate artifact; neither actual marked detector nor actual rank is asserted.

    python3 -B replay_inert19_two_seeds.py | cmp - EXACT-INERT19-TWO-SEEDS.json
    sha256sum -c SHA256SUMS
