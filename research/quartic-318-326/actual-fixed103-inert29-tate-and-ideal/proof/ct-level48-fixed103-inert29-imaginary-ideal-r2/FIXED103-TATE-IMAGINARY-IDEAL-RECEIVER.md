# The odd cubic CM residue depends only on one oriented imaginary quadratic ideal

This refines the exact 29 order-nine-versus-order-dividing-three test. The genuinely moving CM intersection ideal is still unknown. The point is that its oriented valuations would suffice; no separate principal-unit normalization, quartic unit residue or analytic rank converse is needed.

## 1. Descend the relative norm to the odd twist field

Use the previous fixed Tate function $U=(4x^2+9x+3y)/x^2$ pulled back through the literal ordered level-48 map. Let $K=\mathbf Q(\sqrt{D})$ denote the selected imaginary base, $f>1$ the squarefree positive genus conductor, and $L=K(\sqrt f)\subset H_f$ the real-character field over this base. Thus $(D,f)=(-1751,c)$ on the fixed-base route and $(-n/241,241)$ on the moving-base route, both giving $M=\mathbf Q(\sqrt{Df})=\mathbf Q(\sqrt{-n})$ for the first arm. The same statement uses the actual selected $n$ on the companion. Take the two commuting involutions $\sigma$ of $L/K$ and $\iota$ of complex conjugation, and write
$$
 V=N_{H_f/L}(U(P)),\qquad R=V/\sigma V,\qquad W=R/\iota R.
$$
These are nonzero because the fixed-chart unit check even holds after reduction. By construction $\sigma R=R^{-1}$. Hence $\sigma W=\iota W=W^{-1}$, and $W$ belongs to $M=L^{\sigma\iota}$ with quadratic norm one.

At the named place 29, $f$ is square and $D$ inert. Thus the reduction lies in $\mathbf F_{29^2}$ and $\iota$ acts there as 29-Frobenius. Consequently
$$
       \overline W^{280}
           =\overline R^{280(1-29)}
           =\overline R^{560}
           =\gamma^{k\bmod3},
       \qquad \gamma=14+5\sqrt2 .
$$
The middle equality holds because the exponents are congruent modulo $29^2-1=840$. Thus a single cubic residue in the **actual odd imaginary twist field** replaces the quartic ratio. Changing the reference coset or conjugating the chosen orientation inverts the value only. The fixed $(-1751,241)$ calibration gives $\gamma$; it does not compute a moving ideal or assert its order-nine residue.

## 2. An exact valuation input is enough, if oriented

Given the complete fractional ideal $\mathfrak A=(W)$ **in $M$**, recover $W$ up to sign using exact Gauss reduction of the positive definite binary norm lattice of $\mathfrak A$. Indeed each $x\in\mathfrak A$ is uniquely $Wy$, $y\in O_M$; since $N(W)=1$, a nonzero $x$ has norm at least one, and the norm-one vectors are precisely $W O_M^\times$. The actual field has at least the distinct good primes 17 and 103 in its squareclass, so it is not $\mathbf Q(i)$ or $\mathbf Q(\sqrt{-3})$ and $O_M^\times=\{\pm1\}$. Thus the shortest vectors are exactly $\pm W$. At 29, $W$ is a unit and $-1$ is a cube; the cubic residue is independent of the shortest-vector sign. Fractional ideals can be cleared by a common denominator before reduction, using a positive integral Gram matrix and exact rational rescaling.

Equivalently form the oriented ideal of $R$ in $L$ and divide it by its complex-conjugate ideal, then descend the resulting ideal to $M$ using the actual ramification indices. Divisibility of the exponents follows from $W\in M$, not from any unproved ideal class vanishing. The absolute norm of $\mathfrak A$ is always one and contains no phase; replacing a split prime and its inverse conjugate by their product loses the required orientation. Therefore a theorem giving the **signed, conjugation-odd ideal** is sufficient even if it provides no local unit bits. An unoriented absolute factorization is not.

## 3. The exact rational lift has non-CM horizontal zeros

This obviates a possible ambiguity in the previous packet, which excluded CM for the natural torsion tangent lift. Here we treat the actual rational function chosen to define $V$. Its only poles on $E_0$ occur at $T_0$: there $x$ vanishes to order two and $y$ to order one, giving a pole of order three. At $O$ its value is 4. Away from these points, eliminate $y$ using $3y=-(4x^2+9x)$ and $y^2=x(x+1)(x-3)$. All zeros have
$$
           16x^3+63x^2+99x+27=0,
$$
which is irreducible modulo 23 (the replay checks each residue). The 2-adic Newton polygon has a unique slope giving $v_2(x)=-4$. This root is actually in $\mathbf Q_2$: substituting $u_2=16x$ gives $u_2^3+63u_2^2+1584u_2+6912=0$, with simple unit root $u_2=1$ modulo two. Now $s=y/x=-(4x+9)/3$ has depth $-2$ and $4s$ reduces to 1. The two level-48 points above it satisfy $X^2-sX-1=0$, with depths $2,-2$. For the large-$X$ branch, $t_{16}=X-2+3/(xX)$ has depth $-2$; the literal downward formula preserves that depth to $j$.

For the small-$X$ branch, put $w=X/4$. The equation $16w^2-4sw-1=0$ has a simple unit root $w=1$ modulo two, again in $\mathbf Q_2$. So does $(3/(xX))/4$, using $16x$ above. Their sum shows $v_2(t_{16}+2)\ge3$, while $v_2(t_{16})=1$. Also $t_{16}+2\ne0$: the alternate exact formula $t_{16}+2=x/X-X^{-3}$ and the original one would otherwise give $x=X^{-2}$ and $X^2=-3/x$, a contradiction in characteristic zero. Hence $v_2(t_8)<0$ and again the lower charts through $j$ preserve the negative depth. Each possible zero abscissa can be embedded in this 2-adic branch by irreducibility, and both level-48 choices have nonintegral $j$. None is CM.

This confirms why a standard intersection of *two CM cycles* does not supply the missing oriented ideal for this specific $U$. A different function agreeing modulo cubes on the fixed joint chart could still work. The exact unsolved input is either its oriented norm-ideal divisor, or another theorem computing the actual primitive cubic class directly; neither is inferred from the fixed numerical reference.

### Exact replay

The finite check binds the exact cubic predecessor, verifies the genuine horizontal-zero polynomial's irreducibility and valuation list, and gives independent synthetic norm-one residue examples in the fixed reference imaginary field. Those examples are not computations of the actual CM norm ideal.

```sh
python3 check_inert29_imaginary_ideal.py | cmp - EXACT-INERT29-IMAGINARY-IDEAL.json
sha256sum -c SHA256SUMS
```
