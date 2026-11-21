# An exact scalar mod-3 Hecke receiver for the original 13/19 phases

This transfers the exact oriented order-three phase into an ordinary scalar half-integral-weight Hecke eigensystem modulo 3. It does not evaluate an actual detector discriminant or prove simultaneous nonvanishing. The elliptic quotient, CM orientation and degree-two/three flags are the published ones.

## 1. The exact finite Brandt eigenfunction

Let $\ell=13$ or $19$, $X=X_0(48)$, and $S_\ell$ the full set of geometric supersingular labels $(E,C_{16},C_3)$ on $X$ in characteristic $\ell$. Use the same map $\phi:X\to E_0$ to $E_0:y^2=x(x+1)(x-3)$ and define $W_\ell:S_\ell\to\mathbf F_3$ by choosing a generator of the order-three subgroup and reading the coordinate of $[4](1-F_\ell)\phi$, as in the fixed coefficient contract. This is the full oriented chart, not the unmarked $j$ line. Its marked automorphism groups are $\{\pm1\}$: an order-three extra automorphism at $j=0$ has no invariant order-two line; an order-four one at $j=1728$ would need a solution to $x^2=-1\bmod16$ on a stable cyclic order-16 group.

For a prime $p\nmid6\ell$, define the Brandt operator on functions by
$$
(\mathcal B_p W)(E,C_{16},C_3)=
  \sum_{C_p\subset E[p]} W(E/C_p,\overline C_{16},\overline C_3).
$$
Each cyclic line is included with multiplicity, even if different lines give the same oriented label. We have the exact relation
$$
\mathcal B_p W_\ell=a_p(E_0)W_\ell\quad\text{over }\mathbf F_3.
$$
Indeed the nonconstant level-48 quotient of conductor 48 induces the $E_0$-eigenmap on $J_0(48)$ by newform multiplicity one. Write a pointed chart as its degree-zero class relative to the rational cusp $\infty$. For $p\nmid48$, $T_p$ carries this cusp to $(p+1)\infty$ and the other term of the class to the sum of the $p$-quotients with level transported. The two Hecke actions on this degree-zero class therefore compare via $a_p(E_0)$. The map and correspondence specialize at $\ell$, and $[4](1-F_\ell)$ kills any rational basepoint translation. This gives the displayed finite function, not a normalization of a chosen characteristic-zero lift. The matrix of $\mathcal B_p$ is symmetric: dualizing the isogeny reverses an edge, and the marked automorphism sizes on both ends are equal. The Frobenius and $w_{48}$ actions negate $W_\ell$. Also $w_3$ negates it: $3\parallel48$ and the reduction of $E_0$ at 3 is split multiplicative, so the Atkin–Lehner eigenvalue is $-a_3=-1$. The rational translation is again killed. Hence $w_{16}=w_{48}w_3$ fixes $W_\ell$.

An exact independent-of-discriminant control computes all six degree-five Vélu neighbors of every original oriented chart ($96$ at 13, $144$ at 19). It uses the two ordered $t_{16}$ values (before and after the 3-isogeny) to identify each target with its full mark. The replay checks symmetry, all row multiplicities, and $\mathcal B_5 W_\ell=W_\ell$ from $a_5=-2$. The $(-,-,-)$ space under $(F_\ell,w_{48},w_3)$ has dimensions $15,19$ respectively; its $+1$ eigenspaces for $\mathcal B_5$ have dimensions $1,5$. Including the two true old-level trace relations (forgetting from 16 to 8, and forgetting the order-three line) leaves dimensions $1,2$ after imposing the same eigenvalue. The replay binds the already-audited chart and field code and uses no new numerical CM orbit or toy discriminant.

## 2. Scalar character without erasing the marked phase

Write $R_x=\operatorname{End}(E,C_{16},C_3)$, $L_x=R_x^{\mathrm{tr}=0}$ and $Q(v)=\operatorname{nrd}(v)$. In this paragraph the bilinear convention is $B(v,v)=Q(v)$. For $v\in L_x$ with $\alpha_v=(1+v)/2\in R_x$, keep both $0,1$ eigenvalue flags of $\alpha_v$ on $C_{16}[2]$ and keep both flags $b_3=0,1$ on $C_3$. Its Lie derivative is $dv=c\sqrt2$ in the trace-zero line of $\mathbf F_{\ell^2}$; require $c\ne0$. Here 2 is nonsquare at both primes. Let $\xi$ be an odd multiplicative character of $\mathbf F_\ell^\times$, chosen quartic at 13 ($\xi(2)=i$) and quadratic at 19. Its values reduce in $\mathbf F_9$ and $\mathbf F_3$ respectively. Set
$$
\omega(v)=(-1)^{b_3}\xi(c),\qquad
\eta(d)=\left(\frac d3\right)\xi(d\bmod\ell).
$$
The exact finite conditions imply $Q(v)\equiv23\bmod24$. Under multiplication by any integer $d$ prime to $6\ell$, the kept set is preserved and $\omega(dv)=\eta(d)\omega(v)$: at 2 the arms may swap, both being included; at 3 the eigenflag swaps exactly when $d=-1\bmod3$ by $\alpha_{dv}=(1-d)/2+d\alpha_v$; and $dv$ on the tangent line is scaled by $d$. The character $\eta$ is even.

Form the scalar series with signed integer lifts $\widetilde W_\ell=0,\pm1$ of the phase,
$$
H_\ell(z)=\sum_{x\in S_\ell}\widetilde W_\ell(x)
   \sum_{\text{kept }v\in L_x}\omega(v)q^{Q(v)},\qquad q=e^{2\pi i z}.
$$
It is a weight-$3/2$ cusp form with Nebentypus $\eta$ on the safe common group $\Gamma_0(13824\ell^3)$; the latter is a convenient upper level, not a minimality claim. For this, the flags and derivative are unions of cosets of $12\ell L_x$. The matrix-form normalizations of $Q$ on $L_x$ at 2 and 3 are $-a^2-16bc$ and $-a^2-3bc$. At $\ell$ it has form $-2 a^2+\ell u(b^2-2c^2)$ for a local unit $u$ using an unramified lift of the nonsquare 2; away from $2,3,\ell$, use $-a^2-bc$. Accordingly the determinant of $B$ is a positive rational square (its exceptional valuations are $6,2,2$), and the integral lattice level in the convention of [Kane–Kim, Proposition 2.3 and (2.10)](https://link.springer.com/article/10.1007/s00029-025-01110-0) divides $24\ell$. Their common-level coset transformation on a matrix of lower-right entry $d$ sends the label to $d^{-1}$ times the label, with trivial quadratic factor here. Reindexing the weights gives **$\eta(d)$**, not $\eta(d)^{-1}$. The level bound is $4(24\ell)(12\ell)^2$. Cosets whose conductor divides $12\ell$ obey the same transformation by scaling the underlying lattice and using the common upper level.

Cuspidality follows termwise at each fixed 2-arm and Lie value after taking the difference of the two 3-arms: the local norm isometry at 3 interchanges the arms, fixes the zero discriminant coset, and commutes with the Weil action on the same finite quadratic module. The two cusp constant terms agree at every cusp. This is the established marked cusp construction; sums over both 2-arms and odd Lie characters preserve it. The character combination does not symmetrize the 3-arm signs.

At a squarefree fundamental index $n\equiv23\bmod24$ inert at $\ell$, choose the given CM orientation with $d(\sqrt{-n})=c_0\sqrt2$ and the $(0,0)$ flags. Let $\kappa_\ell(n)$ denote the old exact order-three coefficient. The chosen flags and Lie value are exactly one normalized CM orbit by [Cornut–Jetchev, Corollary 4.1 and Remark 6](https://arxiv.org/pdf/1012.0725v1). Passing to the other 2-arm by $w_{16}$ contributes the same weight, passing to the other 3-arm negates the phase and also the external flag sign, and Frobenius negates both the phase and $\xi(c_0)$. All these changes preserve the orientation transport stated here and have the specified multiplicities even when reduced labels repeat. Therefore for the residue coefficient $A_\ell(n)=[q^n]\overline{H_\ell}$,
$$
A_\ell(n)=8\,\xi(c_0)\,\kappa_\ell(n)
$$
in the applicable residue field. The factor is a unit at 3, so this scalar series neither loses nor invents any eligible nonzero phase.

## 3. Full coefficient recurrence by integral pullback of the same endomorphism

The following direct double count avoids both a level-raising hypothesis $3\nmid\ell^2-1$ and any restriction to maximal-order Fourier indices. Let $p\nmid6\ell$ and $m>0$. For each oriented source $x$ and cyclic $p$-isogeny $f:x\to x'$ transport the fixed level subgroups. A kept trace-zero endomorphism $v'$ of the target of norm $m$ pulls back integrally to
$$
u=\widehat f\,v'\, f\in R_x,\qquad \operatorname{nrd}(u)=p^2m .
$$
Its local flags and derivative are those of $p$ times $v'$ in the transported groups, giving $\omega(u)=\eta(p)\omega(v')$. Conversely, pullback from the target for a fixed $u$ is possible precisely when $u/p$ after conjugation by $f$ is integral. Away from $p$ this follows because $f$ is an isomorphism on the local modules; at $p$ use $R_x\otimes\mathbf Z_p=M_2(\mathbf Z_p)$ and its Tate lattice. The prime-to-level quotient corresponds to an index-$p$ superlattice, and for its line spanned by the first vector the changed basis sends
$$
\begin{pmatrix}a&b\\c&-a\end{pmatrix}
 \longmapsto \frac1p
 \begin{pmatrix}a&pb\\c/p&-a\end{pmatrix}.
$$
Integrality is $p\mid a,\ p^2\mid c$.
- If $u\notin pR_x$, its nonzero reduction is nilpotent because its norm is divisible by $p^2$. The only possible line is its kernel. In that frame $p\mid a,c$ and $b$ is a unit; the norm condition forces $p^2\mid c$, so exactly one isogeny works.
- If $u=pv$ with $v\notin pR_x$, integrality is exactly preservation of the line by $v\bmod p$. The nonzero trace-zero matrix with norm $m$ has $1+(\frac{-m}{p})$ eigenlines, including one in the nilpotent case.
- If $p^2\mid u$ every line works: the count is $p+1$. In this case $p^2\mid m$ and the middle quadratic character is zero.

Weighting and summing these three cases counts
$$
 A_\ell(p^2m)+\eta(p)\left(\frac{-m}{p}\right)A_\ell(m)
             +p\,\eta(p)^2 A_\ell(m/p^2).
$$
The second or third term uses the same vectors divided by $p$ or $p^2$, and the same scaled weight; a nonintegral index contributes zero. Alternatively sum the isogenies first at their targets. Symmetry, the literal Brandt eigenfunction and the common scaling factor give $\eta(p)a_p(E_0)A_\ell(m)$. The coefficient at zero vanishes. Thus **the actual scalar cusp form modulo 3 is an eigenform for every good $T(p^2)$**, with eigenvalue $\eta(p)a_p(E_0)$. This agrees with the half-integral-weight coefficient convention in [Kane–Kim, Theorem 2.5](https://link.springer.com/article/10.1007/s00029-025-01110-0); there is no omitted prime-index orientation restriction away from $6\ell$.

## 4. Exact arithmetic still needed

For one already supplied same-index original detector and its shared final prime $q_0$, the required pair is now equivalently
$$
 A_{13}(A_1q_0)\, A_{19}(A_2q_0)\ne 0
$$
in a common residue field, with the actual same $q_0$ and its original CRT. This packet makes the good-prime Hecke eigenstructure explicit, but such a recurrence remains inside one fundamental squareclass. It cannot compute a primitive coefficient at $A_iq_0$ from a normalized good-prime $a_p(E_0)$. The usual Shimura coefficient at index 1 already has the unknown scalar $A_\ell(t)$ for its chosen squarefree $t$. No total-orbit enumeration, class polynomial, candidate selected detector, central derivative or rank is supplied.

### Checksums and replay

Exact order-three contract SHA-256 2b67bc37a0e5514d6acbc977094035a862249f33a42bea6c6cb085591706ac0e; exact cusp target SHA-256 17f6655c3c3607b2c23f14e3059a0cd4555b4ac9ab810d27bbf2e395cfadaac6. The script checks the other input hashes before using them. Its arithmetic replay is entirely finite and tests the full level flags, not a class-number toy.

    python3 -B replay_exact_phase_hecke.py | cmp - EXACT-HECKE-5-LEVEL48.json
    sha256sum -c SHA256SUMS
