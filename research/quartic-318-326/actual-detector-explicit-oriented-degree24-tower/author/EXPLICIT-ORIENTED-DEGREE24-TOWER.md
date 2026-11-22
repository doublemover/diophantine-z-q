# An explicit tower and oriented generator for the moving degree-24 field

This supplies defining equations and the designated generator for the [already published one-companion 5-class criterion](https://github.com/doublemover/diophantine-z-q/tree/8a20b6a4f42d9293c434c50dbcf24430417b78a9/research/quartic-318-326/actual-detector-moving-degree24-five-class-gate). The original fixed projective line field and its half-field are realized without constructing the degree-480 5-division field. The literal selected $n$ and the required class-group dimension are still unknown. No rank, mark, or point is computed.

Write $E_{-1}:y^2=x^3-2x^2-3x$. Use the previously checked full $\mathrm{GL}_2(\mathbb F_5)$ action on $E_{-1}[5]$. For a selected companion $E_n$, the representation is its twist by the rational squareclass $d=-n$. The original $17\mid n$ is squarefree ramification and the base 5-division field is unramified at 17, so it is disjoint from $\mathbb Q(\sqrt d)$, as in the criterion.

## 1. The fixed degree-six line field

Let $P$ be a nonzero geometric 5-torsion point on $E_{-1}$. Put $(x_i,y_i)=(x(iP),y(iP))$ for $i=1,2$, and
$$
 s=x_1+x_2,\qquad q=x_1x_2,\qquad h=x_1-x_2,\qquad H=s^2-4q=h^2 .
$$
Doubling alternates the two x-coordinates, because $4P=-P$. With $F(X)=X^3-2X^2-3X$, the doubling abscissa is $(X^2+3)^2/(4F(X))$. The remainder of $(X^2+3)^2-4(s-X)F(X)$ modulo $X^2-sX+q$ is
$$
 [s^3+6s-(6s-8)q]X+5q^2+(6-s^2)q+9 .
$$
Both coefficients vanish because the remainder vanishes at the two distinct abscissas. Thus $6s-8\ne0$, since $s=4/3$ does not make $s^3+6s$ zero, and the exact sextic and product are
$$
 \begin{split}
 p_6(s)&=s^6-8s^5-60s^4-720s^2+1152s-576=0,\\
 q&=\frac{s^3+6s}{6s-8}.
 \end{split}
$$
An interchangeable polynomial representative in $\mathbb Q[s]/(p_6)$ is
$$
 q=\frac{9s^5-60s^4-620s^3-360s^2-6960s+3888}{2800}.
$$
The value of $s$ determines the two abscissas of the line. Distinct lines cannot share an abscissa, since an abscissa identifies its points up to sign. The full residual image acts transitively on all six lines. There are therefore exactly six conjugate values of $s$, the displayed polynomial is irreducible, and $D=\mathbb Q(s)$ is the degree-six line field. The covector line used in the published criterion is the one with kernel $\langle P\rangle$.

## 2. The two explicit quadratic steps

Choose a primitive fifth root $\zeta$ and set
$$
 \omega=\zeta-\zeta^{-1},\qquad \omega_2=\zeta^2-\zeta^{-2},\qquad
 \sqrt5=\zeta+\zeta^{-1}-\zeta^2-\zeta^{-2}.
$$
The square root notation here specifies this cyclotomic choice, rather than a separately chosen sign. For a member of the line stabilizer let $b$ be its scalar on $P$ and $e$ its determinant. On a covector $\lambda$ with this kernel, the scalar in the convention $\lambda\circ g=a(g)\lambda$ is $a=e/b$: in a basis whose first vector is $P$, the other diagonal entry is both $e/b$ and the covector scalar. The characters $b$ and $e$ independently exhaust $\mathbb F_5^\times$ in the line stabilizer. Its unipotents fix $P$ and $\zeta$.

With $\eta=\sqrt5 h$, the factor $h$ transforms by $b^2\in\{\pm1\}$, and $\sqrt5$ by $e^2$. Thus $\eta$ transforms by $a^2$, and is nonzero. The fixed half-field of the covector extension, unchanged by a quadratic twist, is
$$
 D_2=D(\eta),\qquad \eta^2=5H .
$$
Put $r=y_1\omega+y_2\omega_2$. The action $b=e=2$ sends $(y_1,y_2)$ to $(y_2,-y_1)$ and $(\omega,\omega_2)$ to $(\omega_2,-\omega)$, fixing $r$. It generates the diagonal scalar relation together with the unipotent kernel, so all of $\ker(a)$ fixes $r$. In contrast $b=1,e=-1$ negates $r$. Also $r\ne0$: otherwise $y_1/y_2=-\omega_2/\omega=-(\zeta+\zeta^{-1})$, which lies in $D(\zeta)$ but not $D$. The ordinate ratio lies in $D(P)$ and the intersection of $D(P)$ and $D(\zeta)$ is $D$, by the independence of the characters $b$ and $e$. The ratio is defined since neither ordinate of nonzero 5-torsion is zero. This proves that $D(r)$ is precisely the quartic covector field over $D$ and $r$ gives its final quadratic step over $D_2$.

For explicit coefficients let
$$
 S=s^3-3sq-2(s^2-2q)-3s,\qquad k=s^2-q-2s-3 .
$$
Then $y_1^2+y_2^2=S$ and $y_1^2-y_2^2=kh$. The tangent formula for $y_2$ gives
$$
 4y_1y_2=-4F(x_1)+2F'(x_1)(2x_1-s)=h^3 .
$$
Indeed the remainder of $-4F(X)+2F'(X)(2X-s)-(2X-s)^3$ modulo $X^2-sX+q$ is $s^3+6s-(6s-8)q=0$. The cyclotomic identities
$$
 \omega^2=(-5-\sqrt5)/2,\qquad
 \omega_2^2=(-5+\sqrt5)/2,\qquad \omega\omega_2=-\sqrt5
$$
now yield
$$
 \alpha=r^2=-\frac{5S+(k+H)\eta}{2}.
$$
The required moving field is therefore given by
$$
 \boxed{A_n=D_2(r_n),\qquad r_n^2=d\alpha,\qquad d=-n.}
$$
Indeed $r_n=\sqrt d\,r$ has the twisted covector kernel: the kernel condition for its stabilizer is $\chi_d a=1$; the square character still fixes $D_2$. Independence of the quadratic field from the base division field also gives $r_n\notin D_2$. Equivalently, a single quartic for $r_n$ over $D$ is
$$
 X^4-5nSX^2+\frac{n^2}{4}\bigl(25S^2-5H(k+H)^2\bigr).
$$

## 3. The generator is scalar 2, not its inverse

In the base line stabilizer take $b=1,e=2$ and lift it to fix $\sqrt d$, possible by the disjointness at 17. Its scalar on the twisted covector is then $a=2$. It negates $\eta$ and sends $r$ to $y_1\omega_2-y_2\omega$. Multiplying the two values and using $4y_1y_2=h^3$ gives $r\sigma_2(r)=\eta(H/4-k)$. Consequently the required action on the actual tower is
$$
 \boxed{\sigma_2(s)=s,\qquad \sigma_2(\eta)=-\eta,\qquad
 \sigma_2(r_n)=\frac{d\eta(H/4-k)}{r_n}.}
$$
Both radicals are nonzero, and $H/4-k\ne0$ since $r\sigma_2(r)\ne0$. The exact identity $\alpha\bar\alpha=5H(H/4-k)^2$ also checks that this formula respects the quadratic relation; the bar negates $\eta$. Applying it twice sends $r_n$ to $-r_n$, confirming the cyclic quartic order. The eigencondition in the published class criterion is still $W(\sigma_2\mathfrak a)=2W(\mathfrak a)$ with this named action on ideals. Replacing $\sigma_2$ by its inverse would change the test.

## Portable replay and scope

The standard-library replay checks the symbolic remainder, elimination and norm identities over the rationals. Its two fixed controls use $P\in E_{-1}(\mathbb F_\ell)[5]\setminus\{0\}$ at $\ell=127,157$, where $\ell=2\pmod 5$. In the four-dimensional cyclotomic residue extension, literal arithmetic Frobenius fixes $P$ and sends $\zeta$ to $\zeta^2$; the replay checks its oriented action on $\eta,r,r^2$ and the product formula. These are base-field arithmetic controls only, not tests of any selected arithmetic input, a class-group computation, or a rank result.

```sh
sha256sum -c SHA256SUMS
python3 -B replay_explicit_tower.py | cmp - EXACT-EXPLICIT-TOWER-CONTROLS.json
```
