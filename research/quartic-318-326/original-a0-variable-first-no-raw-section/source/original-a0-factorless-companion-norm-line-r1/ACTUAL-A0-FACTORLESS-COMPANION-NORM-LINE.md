# One norm-line descent on the unchanged input-0 scalar

This is the fixed first chart \(z=1/100\) at the **already pinned original** scalar, not a new source index or a detector control. Its stronger ordered companion is equivalent to one explicit quartic square at a rational norm-one parameter. Eight natural signed lifts with rotation \(+3\) or \(-3\) fail, even though all eight pass the four actual poles of the compact normalizer. The unrotated products fail as well. Neither arbitrary rotations nor other raw marks are excluded, and no rational companion point is given.

## 1. Literal coefficients and exactly what the norm line represents

Keep \(h=473592745039516333133760\), \(i=6^{15}3^{65536}J\), and the frozen \(J\) from the pinned source. Write \(R=4376874610839020\), \(D=1+114444R=500907037962860804881\),
\(\beta=204618888056724185\), \(c=12W/D\), \(\mu=\beta c^2\), \(B=289\mu\) and \(a=17/100\). Thus \(B=17b=\beta(17c)^2\), with \(b\) literally the original scalar label, not a new quadratic parameter. In the fixed factorless chart, the companion parameter is
\[
 \lambda=\frac{(1-\mu)(1-a^2\mu)(1-9a^2\mu)}
                       {(1+3a^2\mu)^2}.
\]
Positivity follows from the original real scalar guard \(0<\mu<1\) and \(9a^2<1\).

Let \(r^2=\beta\). For \(\varepsilon_1,\varepsilon_2\in\{\pm1\}\) the element
\[
 A+Gr=\frac{(1+cr)(1+\varepsilon_1acr)(1+3\varepsilon_2acr)}
                 {1+3a^2\mu}
\]
has norm \(\lambda\). The first sign \(+\) chooses one representative per global conjugation; changing it and conjugating replaces a rotation parameter \(t\) by \(-t\). Explicitly,
\[
 A=\frac{1+(\varepsilon_1a+3\varepsilon_2a+
                 3\varepsilon_1\varepsilon_2a^2)\mu}{1+3a^2\mu},
\qquad
 G=\frac{c(1+\varepsilon_1a+3\varepsilon_2a+
                 3\varepsilon_1\varepsilon_2a^2\mu)}{1+3a^2\mu}.
\]
All rational norms \(\lambda\) are obtained, from any one such seed, by multiplication by \((1+tr)/(1-tr)\) for \(t\in\mathbf P^1(\mathbb Q)\): a norm-one element \(u\ne-1\) gives \(t=(u-1)/(r(u+1))\in\mathbb Q\), and \(u=-1\) is \(t=\infty\). The rotated coefficients are
\[
 A_t=\frac{A(1+\beta t^2)+2\beta Gt}{1-\beta t^2},\qquad
 G_t=\frac{G(1+\beta t^2)+2At}{1-\beta t^2}.
\]
The denominator cannot vanish at any rational finite \(t\), as \(\beta\) is not square.

The stronger ordered companion means precisely a point on
\(E_{\beta\lambda}: y^2=x(x-\beta\lambda)(x+3\beta\lambda)\) with
\(([x],[x-\beta\lambda],[x+3\beta\lambda])=(\beta,1,\beta)\) in squareclasses and no zero coordinate. It exists if and only if
\[
                   F_t=4A_t^2-3\beta G_t^2
\]
is a rational square for some \(t\), with \(A_tG_t\ne0\). In fact \(A_t^2-\beta G_t^2=\lambda\), and \(A_t^2+3\lambda=F_t\). For \(k^2=F_t\), one obtains the companion point on the original fixed quartic as \(v=A_t,\ w=17c\,\beta G_t k\); conversely a point with the stated ordered class has \(v^2-\lambda=\beta G_t^2\) and \(v^2+3\lambda\) square. Clearing the explicit square denominator \((1-\beta t^2)^2\) gives a four-degree polynomial in \(t\) with exact compact rational coefficients. Its solvability is stronger than the PointPair requirement, which only prescribes the first of those three classes.

## 2. All actual poles from the fixed normalizer, and a false local candidate

The complete, simple prime factorization of the compact normalizer is
\[
                    D=29\cdot181\cdot1346909\cdot70850399941 .
\]
The source replay uses the literal untouched \(\mathbb F_{p^2}\) elliptic point, chart and indices. At \(29\), both source multiples reduce to the identity. Their formal parameters have ratio \(i/h\equiv11\bmod29\). Indeed both are multiples in the formal group of the same first formal multiple, and the multiplication series has linear term equal to the multiplier. The chart \(2y/(x^2+(3-r_2)^2)\), \(r_2^2=2\), has linear term \(-2\) in the parameter \(-x/y\). Thus the two chart values have the same ratio, and the norm gives \(Q_{\rm pack}\equiv11^2/R^{15}\). All other normalizer sites are regular, with denominator and norms units checked by the affine replay. In order the exact \(W\) residues are
\((12,146,429536,66349154550)\). In particular \(v_p(c)=-1\) at all four; this claims no completeness of poles arising internally in \(W\).

At such a site \(p\ne2,3,5,17\), the leading coefficient formulas give \(pA=0\bmod p\) and \(pG=\varepsilon_1\varepsilon_2\,pc\bmod p\). Also \(v_p(\lambda)=-2\) with stripped residue \(-\beta(pc)^2\), nonsquare at 181. Thus the fixed companion has no branch with zero ordinate. For unit \(1-\beta t^2\), the stripped square test at \(v_p(t)\ge0\) is, whenever its numerator is a unit,
\[
 p^2F_t\equiv
 \frac{(pG)^2\,\beta(3-\beta t^2)(3\beta t^2-1)}
      {(1-\beta t^2)^2}\pmod p .
\]
For \(t=0\), the signs across the four primes are \(+,-,-,+\), independent of the signed seed (the same unrotated square test at \(\infty\) only changes both coefficients' signs). For \(t=\pm3\), this is a nonzero square at all four and every denominator is a unit. This is only passing those four sites.

## 3. Two independent exact unit obstructions on the same \(c\)

All these \(\pm3\) lifts fail without changing the original scalar. At 13 and 19 both source multiples are again formal, and the same formal ratio rule gives \(i/h\) integral, with residue respectively \(0,5\). The ratio being zero at 13 means \(Q_{\rm pack}\equiv0\), not an undefined chart. This gives \(W\equiv1,2\), hence the **actual** \(c\equiv8,1\), respectively. All denominators in the norm-line evaluation are units at these two places.

| \((\varepsilon_1,\varepsilon_2)\) | \(F_{+3}\) mod 13 | \(F_{-3}\) mod 13 | \(F_{+3}\) mod 19 | \(F_{-3}\) mod 19 |
|---|---:|---:|---:|---:|
| \(+,+\) | 1 | 5 | 14 | 7 |
| \(+,-\) | 5 | 1 | 2 | 15 |
| \(-,+\) | 5 | 5 | 2 | 17 |
| \(-,-\) | 1 | 12 | 14 | 14 |

Every entry in the \(+3\) column at 19 is nonsquare. At \(-3\), the two entries 7 and 17 **are squares at 19**, but both corresponding entries are 5, a nonsquare at 13. The other two \(-3\) entries fail at 19. Via the simultaneous conjugation already noted this covers all eight starting sign choices with either rotation. It is not a failure of local solubility of the quartic: it rejects these particular rational parameters, not a \(p\)-adic open search or a global higher descent.

The exact scalar pin is byte-identical to the [archived literal scalar-fibre donor](https://github.com/doublemover/diophantine-z-q/tree/f767adfb8eba61b98fc865e82f73776f4f095799/research/quartic-318-326/actual-original-pointpair-kummer-fibre/ct-original-scalar-kummer-fiber-r1). That donor has the separate \(\lambda'=1+3\mu\), not the \(\lambda\) tested here. No giant coordinate was expanded, and neither detector-specific primes nor an alternate scalar were chosen.

~~~sh
sha256sum -c SHA256SUMS
python3 -B replay_actual_norm_line.py | cmp - EXACT-NORM-LINE-LOCAL-ROWS.json
~~~
