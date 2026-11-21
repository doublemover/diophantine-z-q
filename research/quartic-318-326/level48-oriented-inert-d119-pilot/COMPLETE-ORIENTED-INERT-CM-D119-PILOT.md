# A complete inert CM trace pilot at level 48: $D=-119$, $\ell=29$

This is an exact **toy** implementation of the oriented input and finite nonvanishing check of the fixed-level Heegner certificate. It is not a literal detector $b$, an original rank result, or an estimate for a huge original class group. Neither a Hilbert class polynomial nor a characteristic-zero CM coordinate is used.

## 1. One explicit oriented reduction seed

Work over $F=\mathbb F_{29}[\sqrt2]$. The prime 29 is inert for $D=-119$, while $D\equiv1\bmod24$ and 2 and 3 split in $K=\mathbb Q(\sqrt D)$. The seed curve is $A:y^2=x^3+1$ over $\mathbb F_{29}$, with $30$ points and $\pi^2=[-29]$ for its $\mathbb F_{29}$-Frobenius. Let $\rho(x,y)=(\zeta x,y)$ for $\zeta=14+5\sqrt2$, of order 3. Thus $\rho^2+\rho+1=0$, and $\pi\rho=\rho^{-1}\pi$. The exact endomorphism
$$
 \omega=1+\rho+\pi
$$
satisfies $\omega^2-\omega+30=0$: $1+2\rho$ squares to $-3$ and anticommutes with $\pi$, so $2\omega-1$ squares to $-3-4\cdot29=-119$. The order generated is the maximal $O_D$; this is an explicit optimal orientation, which lifts by Deuring to one CM seed. Either compatible characteristic-zero seed class gives the same trace because the full ideal orbit is taken.

Fix the level ideal $\mathfrak n=\mathfrak p_2^4\mathfrak p_3$ for $\mathfrak p_2=(2,\omega)$ and $\mathfrak p_3=(3,\omega)$. The reduced primitive forms show $h(-119)=10$. Using the even root of $z^2-z+30$ modulo $2^k$, the norm form of $\mathfrak p_2^k$ reduces for $0\le k\le5$ to
$$
 (1,1,30),(2,1,15),(4,-3,8),(4,3,8),(2,-1,15),(1,1,30).
$$
The form of $\mathfrak p_3$ is $(3,1,10)$, outside this subgroup. Thus the ten classes $\mathfrak p_2^k\mathfrak p_3^j$, $0\le k<5,\,0\le j<2$, are all class indices, not merely ten sample points.

## 2. Finite kernels and actual nested level coordinates

The code finds one primitive point of order $2^8$ and one of order $3^2$ on their selected $\omega$-eigenlines. The roots of $z^2-z+30$ selected by the level are $162\bmod256$ and $3\bmod9$. For a group element of the right primary torsion, applying $\omega-(1-r)=r+\rho+\pi$ puts it on the eigenspace of root $r$; its order and eigenvalue are both checked by exact group operations. The extra powers allow computation through the two-dimensional array of degree-2 and degree-3 quotient curves and their order-48 level flags. Those temporary torsion coordinates are in $F[T]/(T^{64}-8\sqrt2)$ and $F[T]/(T^3-\zeta)$, respectively; the polynomials are irreducible since a root has exact order 512 or 9 and the orders of 841 modulo 512 and 9 are 64 and 3. The kernels of each single quotient and all final level moduli coordinates are already over $F$. The successive quotients use exact Vélu point formulas. Transporting the generating points through the actual quotient retains the named prime-ideal direction. There is no resetting of a cyclic isogeny to an unoriented edge in a $j$-graph.

Here is the necessary level-coordinate disambiguation. At level 2 put the kernel root at 0, so $y^2=u(u^2+a u+b)$; the source Hauptmodul is $t_2=256b/(a^2-4b)$. For the *chosen* order-four subgroup, let $u$ now denote the translated $x$-coordinate of either primitive generator, so $u^2=b$. The exact source level-4 Hauptmodul is
$$
                           t_4=\frac{64u}{a-2u}.
$$
Indeed the two adjacent level-2 values are $t_4^2/(t_4+16)$ and $t_4(t_4+16)$ by the quadratic model and the quotient root $a+2u$. This verifies the formula as a rational function, hence also at the evaluated finite points. Merely matching the two adjacent $t_2$'s can be ambiguous, and is not the verifier's rule here.

The two degeneracy values of $t_8$ are $t_8^2/(t_8+4)$ and $t_8(t_8+8)$. In the Appendix A source the printed $+4$ in the **second** one is corrected by the same source's Atkin–Lehner relation: $w_4\pi_1 w_8$ with $w_4(s)=256/s$, $w_8(t)=32/t$ gives $t(t+8)$. Likewise the level-16 values are $t_{16}^2/(t_{16}+2)$ and $t_{16}(t_{16}+4)$. Each inverse match at levels 8 and 16 for this pilot is checked to have exactly one solution in $F$; no generic uniqueness is assumed.

Finally, on the modular model $Y^2=X^8+14X^4+1$ put $y_{48}=(Y+X^4+1)/2$. The source and target of the 3-isogeny, *with the same 16-level flags*, give the pair
$$
          \left(X-2+\frac{3X}{y_{48}},\
                 \frac{y_{48}-2X-1}{X}\right).
$$
These are the published forgetful maps $X_0(48)\to X_0(16)$; the second can also be derived from $w_{16}\pi_1w_{48}$. Each of the ten actual input pairs has exactly one match in the noncuspidal affine chart over $F$, verified by complete enumeration of this fixed small chart. The four points with $X=0$ or $X=\infty$ are cusps from the divisor of $X$; a CM elliptic curve with potentially good reduction does not reduce to a cusp. This step identifies the full $X_0(48)$ points, not just $j(A),j(A/C)$. See [Colò, Appendix A, pp. 234–237 and 247–248](https://www.leonardocolo.com/documents/thesis/PhD_Thesis.pdf). Prime-to-29 ideal kernels commute with reduction, so Deuring's lift and the class enumeration show that this is one complete oriented reduced CM orbit, with all multiplicities retained.

## 3. Exact output and scope

For $\phi$ the explicit degree-two map to $E_{-1}$ of the fixed-level certificate, the finite trace and its torsion-annihilated value are
$$
             \bar P=(27,16\sqrt2),\qquad [4]\bar P=(17,24\sqrt2)\ne O .
$$
There is no height computation or roundoff. Choosing $\sqrt{-119}=10\sqrt2$ in this residue field, the latter descends to $(7,10)$ on the reduction of $E_{119}$. In characteristic zero the finite witness is sufficient for positive rank by the anti-invariant trace argument of the fixed-level certificate. As a distinct check, $(1344,52920)$ is a literal rational point on $E_{119}$, with nonzero ordinate; ramified twists at both 7 and 17 bound the torsion as in that certificate.

The computations are a small proof-producing pilot. Even with fixed degree 48 and fixed $\mathbb F_{\ell^2}$ for the moduli points, an actual detector would still need its exact discriminant, a certified oriented seed, a complete orbit or a correctly normalized multiplicity calculation, and a nonzero sum. This pilot makes no claim about supplying them at an original pole. It also does not use extension fields of these toy degrees as a general complexity bound.

The fixed-level certificate is pinned by paper SHA-256 `f1ffe375bf6fe92afe707d06f88dfc6bef2bb2da80532f48cc939f65e395104c`. The replay uses Python and NumPy; NumPy operations are integer polynomial convolutions, not floating-point approximations.

    python3 -B replay_inert_cm_pilot.py | cmp - EXACT-INERT-CM-PILOT.json
    sha256sum -c SHA256SUMS
