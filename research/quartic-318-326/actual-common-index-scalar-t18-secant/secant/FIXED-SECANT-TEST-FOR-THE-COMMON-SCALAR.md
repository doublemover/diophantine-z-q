# The common-index scalar has one fixed secant-quartic test

Keep the actual common-index input-zero scalar, its literal positive $\delta=1-\beta c^2$, and the fixed $t=18$ first point $P$ on $F=E_n$ from the relative-isogeny reduction. The exact raw obstruction for this first choice was $\kappa_x=\phi_*(\kappa)$, with $\kappa$ the relative Sha class on $E_{n\delta}$ of the full ordered mark and $\phi$ the zero-root 2-isogeny. This note gives a concrete polynomial that decides whether $\kappa_x=0$. It does not compute such a decision. Two available finite-level operations are specifically insufficient.

## 1. The exact trace target on the fixed isogenous curve

Let $\phi_0:F\to G_0=E'_n$ be the untwisted same zero-root isogeny, in the conventions
$$
 G_0:y^2=f(x)=x^3-4nx^2+16n^2x,\qquad
 \phi_0(u,v)=(u+2n-3n^2/u,\ v(1+3n^2/u^2)).
$$
The twist identifications commute with these maps. If $\delta$ is square the companion is immediate from the known $P$. Otherwise $K=\mathbb Q(\sqrt\delta)$ is quadratic and the relative cocycle for $\kappa$ is labelled by $P$ in $F(\mathbb Q)/\operatorname{Tr}F(K)$. Pushing forward by the isogeny sends that label to
$$R=\phi_0(P)=(r,s)\in G_0(\mathbb Q).$$
The same twist cohomology on the isogenous curve gives
$$\kappa_x=0\quad\Longleftrightarrow\quad R\in\operatorname{Tr}_{K/\mathbb Q}G_0(K).$$
In particular $R$ is already an everywhere-local trace. It is nontorsion because $P$ is nontorsion and $\phi_0$ is an isogeny.

Also $R$ is **not** a rational double. If $R=2Q$ over $\mathbb Q$, then $P-\hat\phi_0Q$ is in the kernel $\{O,(0,0)\}$ of $\phi_0$, since $\phi_0\hat\phi_0=[2]$. The dual isogeny image has x-class 1, and the kernel has x-classes 1 and $-3$. This contradicts the positive nonsquare x-class $\beta$ of $P$.

## 2. A single quartic of fixed coefficients

Define
$$
 \Delta_R(m)=(3r-4n-m^2)^2
       -4(3r^2-8nr+16n^2+2ms).
$$
For $\delta$ nonsquare the exact equivalence is
$$
 \boxed{\quad \kappa_x=0\quad\Longleftrightarrow\quad
           \Delta_R(m)=\delta z^2\text{ for some }m,z\in\mathbb Q,\ z\ne0.\quad}
$$

To verify this, suppose $U+\sigma U=R$ on $G_0(K)$. Neither summand is the identity (else $R=O$), and their abscissas differ. If abscissas agreed, they would either be opposites, giving $R=O$, or equal as points, giving a rational double. The secant is therefore nonvertical, fixed by conjugation, and passes through $-R$. It has rational equation $y=m(x-r)-s$. Write $X=x-r$. Its cubic intersection equation is exactly
$$
 f(r+X)-(mX-s)^2
 =X\bigl[X^2+(3r-4n-m^2)X+(3r^2-8nr+16n^2+2ms)\bigr].
$$
The two nonrational conjugate roots of the residual quadratic have discriminant $\delta z^2$ with $z\ne0$. Conversely this discriminant condition gives two distinct nonrational conjugate points from the quadratic and the stated line. They sum to $R$ by the chord law, so their trace gives the class vanishing.

The quartic is separable: the four geometric halves of the nontorsion $R$ give four distinct tangent lines through $-R$, with distinct finite slopes (a line cannot be tangent at two distinct points and also pass through $-R$). They are the four discriminant-zero slopes. There are no rational discriminant-zero slopes, since a repeated quadratic root would be rational and give a rational half of $R$. At infinity the smooth quartic has the two points defined by $z^2=1/\delta$ in the normalized infinity chart, neither rational for nonsquare $\delta$. Thus a rational point on the smooth projective quartic is also an exact certificate, without hidden affine exceptions.

For the fixed $P=(u,v)$ put $a=v/u$. Then $r=a^2=u+2n-3n^2/u$ and $s=a(u+3n^2/u)$. Expanding gives the exact factorization
$$
 \boxed{\quad
 \Delta_R(m)=\bigl((m-a)^2-4u\bigr)
             \bigl((m+a)^2+12n^2/u\bigr).
 \quad}
$$
These two quadratic factors have discriminant squareclasses $\beta$ and $-3\beta$ respectively. For example $u=\beta A^2$ and $\delta=1-\beta c^2$ make the first factor equal to $\delta(2A/c)^2$ at $m=a\pm2A/c$. This is an **optional** choice, not an equivalence: it leaves the other factor to be a square and there is no established rational square there. In general the exact criterion is the whole product, not separate prescribed squareclasses on its factors.

Equivalently one may use an integral fixed curve and quartic. Put $N=nA^2$, $R_1=rA^2$, $R_2=sA^3$, where the replay checks that all three are integers. Then in slope $M=Am$ the integral polynomial is
$$
 M^4+(8N-6R_1)M^2-8R_2M-3R_1^2+8NR_1-48N^2.
$$
It needs to equal $\delta Z^2$ for rational $M,Z$, where $Z=A^2z$. The fixed polynomial uses only the pre-existing $P,n$; the literal source enters only through the one factor $\delta$. No support factorization is needed to state or verify such a point certificate.

## 3. The prepared-prime Cassels and restriction barriers

Writing $G=E'_{n\delta}$, the obstruction lies in $\Sha(G)[\hat\phi]$. Cassels--Tate adjunction gives
$$ \langle\kappa_x,\xi\rangle_G
       =\langle\kappa,\hat\phi_*\xi\rangle_{E_{n\delta}} .$$
Thus the pairing **always vanishes** on every partner in $\Sha(G)[\hat\phi]$; evaluating only that kernel cannot detect the class. More specifically, for a 2-torsion partner $\xi\in\Sha(G)[2]$, the possible image $\hat\phi_*\xi$ is in $\Sha(E_{n\delta})[\phi]$ because $\phi\hat\phi=[2]$. A nonzero pairing would require nonzero such image. Its isogeny Selmer preimages are precisely pure-second classes in the full ordered descent, by the zero-root Kummer diagram. The uniform fixed-support result shows that no nontrivial such preimage is supported solely on the fixed primes of $n$; it needs unseen odd-depth primes of the literal $\delta$ congruent to $1$ modulo 3. The controlled support supplies no such partner. This does not exclude partners with new support or tests involving higher torsion.

Restriction of $\kappa_x$ to $K$ is already zero, so corestricting that equality recovers only $2\kappa_x=0$. In contrast, triviality over a verified odd-degree extension would force zero by restriction--corestriction, but no such splitting extension is supplied. The prepared local data already make the class everywhere locally trivial and do not give global splitting.

One must also not replace vanishing by evidence of divisibility. Let $s_x\in\operatorname{Sel}_2(G)$ be the image of the original ordered Selmer class under $\phi$ on full 2-torsion. For each $j\ge2$ the precise implication of a higher lift is
$$
 s_x\in\operatorname{im}\bigl(\operatorname{Sel}_{2^j}(G)
                         \longrightarrow\operatorname{Sel}_2(G)\bigr)
 \quad\Longleftrightarrow\quad
 \kappa_x\in 2^{j-1}\Sha(G)[2^j].
$$
The forward implication is the Kummer exact sequence with the map $[2^{j-1}]$; conversely lift a Sha preimage to the higher Selmer group and correct the residual difference by the lift of a rational Mordell--Weil Kummer class. A nonlift would prove nonzero. A lift to a fixed level, or even indefinite divisibility without a Sha finiteness/exponent result, is not proof of zero. If the entire ordinary 2-Cassels row were zero, its radical criterion would give only the Selmer-four image, for this purpose.

Thus the bounded controlled-prime operations above do not determine the raw mark. A genuine rational point on the fixed secant quartic decides zero exactly; a nonzero Cassels pairing against an admitted partner, or a certified higher nonlift, decides nonzero. No such global observable is evaluated here, and no statement is made about other choices of the first twist.

## Exact bindings and replay

- Common-index scalar and relative isogeny class: list `173d6f342c7a87f71430fe6cb7b2799cc02da878f771095c55cef238d6f3c158`.
- Fixed $t=18$ known first rational point and trace comparison: list `16ba82294a3aeef50bfd7182c33ab01fa04a3e541238e2870be2901b3cdb312b`.
- Pure-second unseen-support reduction: list `66b5e1c5e01763abfbc6a060d5889621ee07580158a73c393017db091e5f27d3`. Only its beta and dyadic rows are used uniformly, not any archived extra ramification.

The standard-library replay verifies only the fixed first point, exact isogeny coordinates, quartic factorization and integral coefficient model. No new prime test, actual $\delta$, point search, or rank computation is performed.

```sh
sha256sum -c SHA256SUMS
python3 -B replay_t18_fixed_secant.py | cmp - EXACT-T18-FIXED-SECANT.json
```
