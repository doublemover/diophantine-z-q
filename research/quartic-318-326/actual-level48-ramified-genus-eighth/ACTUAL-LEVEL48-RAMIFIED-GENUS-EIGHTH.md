# The raw unweighted level-48 trace is a rational eighth multiple

Let $n$ be an actual selected detector twist on which the published rational-fourth result applies. Keep the literal Selmer basis of size eight with non-torsion line $M=(\beta,1)$ in $(x+3n,x-n)$ coordinates. Fix a genuine prime $p_\beta\mid\beta$ different from 17 and from the actual final $q_0$, and four further distinct genuine primes $p_1,\ldots,p_4$ in $n$, all $1\bmod24$. They exist because the original seven-prime $\beta$ is 17 plus six genuine distinct primes. More generally the argument takes these conditions and the size-eight basis as hypotheses; it does not require the shorter twists below to have a size-eight Selmer group. In this scope **every raw unweighted trace lies in $8E_n(\mathbf Q)$**. In particular the already available cyclic-four comparison always has equal marks. This neither implies vanishing of the raw trace nor produces a rational marked eighth.

## 1. Four genus characters, retained places, and weighted quarters

Put $D=-n$, $K=\mathbf Q(\sqrt D)$, $E_0:y^2=x(x+1)(x-3)$ and retain the same actual raw degree-two modular map $\phi$ with $\phi w_{48}=T_3-\phi$. For each subset of the four primes let $\Delta$ be its squarefree product. Both $\Delta$ and $D/\Delta$ are fundamental discriminants when $\Delta>1$, because they are squarefree, odd, $1\bmod4$ and coprime; also $n/\Delta\equiv23\bmod24$. The corresponding genus characters on the Hilbert class field are independent: no nontrivial product $\Delta>1$ of these real squareclasses becomes square in the imaginary quadratic $K$. Let
$$
 H_0=K(\sqrt{p_1},\ldots,\sqrt{p_4}).
$$
It is inside the Hilbert class field $H$ by the genus construction. It is unramified at 2 and 3 over $\mathbf Q$ because $K$ is split there and $H/K$ is unramified. Every such character is $+1$ on the chosen level-48 ideal, since its radicand is $1\bmod24$.

Write $A$ for the **literal indexed sum** of $\phi$ on the all-positive genus slice, $P=P(n)$ for its unweighted full trace, and $R_\Delta$ for the same full orbit weighted by character $\chi_\Delta$. Orthogonality is the exact group identity
$$
 16A=P+\sum_{\Delta>1}R_\Delta .
$$
All terms lie in $E_0(H_0)$. Also $R_\Delta$ lies in the embedded rational twist $E_{n/\Delta}(\mathbf Q)$: the class action has character $\chi_\Delta$, and complex conjugation is minus by the modular identity, because $\chi_\Delta(\mathfrak n)=+1$ and the nontrivial character sum kills the $T_3$ translate. The full trace $P(n/\Delta)$ on the induced orientation of the shorter quadratic field lies in the same twist: its class number is even. Primarily, that class number is divisible by four from the independent ramified ideal classes at 17 and $p_\beta$; the norm argument gives $17p_\beta<(n/\Delta)/4$ since in particular $q_0\equiv7\bmod24$ remains. The exact conjugation formula then kills the $T_3$ translation there as well. The canonical identifications of the four rational 2-torsion points of the different twists with $E_0[2]$ use their named roots; both choices of square root give the same identification.

Use the independently checked same-map genus Gross–Zagier comparison: if $R_\Delta$ is nontorsion then the shorter rational twist has rank one by Gross–Zagier and Kolyvagin, $P(n/\Delta)$ is nontorsion, and their signed free coefficients $m,m'$ satisfy
$$
 v_2(m/m')\geq \omega(\Delta)+1.
$$
The exact primary height ratio is $(m/m')^2=4^{\omega(\Delta)}\mathcal L(-\Delta)/\mathcal L(-1)$; its nonzero even central normalization is an even square by Feng–Liu–Pan–Tian, Proposition 2.6(i). This ratio needs the removed $\Delta\equiv1\bmod24$, not that every retained prime be individually $1\bmod24$. The retained twist is still squarefree, prime to 6, $23\bmod24$, with the same split level 2 and 3, and the same degree-two modular map. The weighted and shorter points may be zero; no nonvanishing is used without this case split.

Every involved rational twist has torsion exactly $(\mathbf Z/2)^2$ by the exact split Tate calculation at 3: minimal multiplicative discriminant depth 2, $-c_6\equiv1\bmod3$, Tate valuation quotient $\mathbf Z/2$, and unit kernel $\mathbf Z_3^\times$ with torsion $\{\pm1\}$. Thus one may write
$$
 R_\Delta=4Q_\Delta+T_\Delta,\qquad T_\Delta\in E_0[2],
$$
with $Q_\Delta$ on that same rational twist. In the torsion branch take $Q_\Delta=O$. Otherwise $m$ is divisible by four and the free coordinate of $Q_\Delta$ is $m/4$. Since $(m/4)/m'$ has nonnegative 2-adic valuation, there are an odd integer $a_\Delta$, an integer $b_\Delta$, and $T'_\Delta\in E_0[2]$ such that
$$
 a_\Delta Q_\Delta=b_\Delta P(n/\Delta)+T'_\Delta .
$$
In the torsion branch take $a_\Delta=1$, $b_\Delta=0$, $T'_\Delta=O$. The same actual torsion point in this relation specializes at both primes. No inference that the weighted point is itself divisible by four without torsion is needed.

## 2. Both ramified reductions of the quarters agree in their 2-part

Choose places of the common $H_0$ above $p=q_0$ and $p=p_\beta$, and extend each as needed to reduce its actual full/shorter orbit. The shorter $P(n/\Delta)$ reduces to $O$ at both retained ramified primes. The original ramified-pair argument applies without Selmer hypotheses to the shorter twist: $\chi_{17}(\mathfrak n)=-1$, inertia and complex conjugation act trivially on $\mathbf Q(\sqrt{17})$ at these $p\ne17$, so the level-inertia index involution is fixed-free and each pair reduces to $T_3$. The shorter $h'\equiv0\bmod4$ makes the pair sum zero. This uses characteristic-zero indices, not a count of distinct geometric reductions.

Reduce the odd-denominator relation at each place, in a finite residue elliptic group. Project to its 2-primary subgroup; the projection commutes with integer multiplication and acts as the identity on $E_0[2]$. Multiplication by odd $a_\Delta$ is invertible on that subgroup and fixes $E_0[2]$, so the exact 2-primary reduction of $Q_\Delta$ is $T'_\Delta$ at **each** place. The four torsion points here are compared by their named roots, never by a place-dependent choice of lift, twist sign, or decomposition generator.

For $A$, the same inertia–Fricke relation preserves this particular genus slice at both retained places. Indeed the radicands are unramified there and real, and each genus character is $+1$ on the actual level ideal. The index relation is $\phi(\bar x_{\mathfrak a})=T_3-\phi(\bar x_{B\mathfrak a^{-1}})$ on reductions with an index permutation of the slice. Summing gives $2\widetilde A=(\#\mathrm{slice})T_3$, so $4\widetilde A=O$ without assuming the size of the slice is even.

## 3. Descent of the eighth and exact scope

The original selected trace already has a rational quarter: $P=4B$ in $E_0(K)$ with $B$ the image of a rational point $B_D\in E_n(\mathbf Q)$. Substituting into the orthogonality identity gives
$$
 4(4A-B-\sum Q_\Delta)=\sum T_\Delta\in E_0[2].
$$
An order-four point on $E_0$ has double equal to one of $(0,0),(-1,0),(3,0)$. By the rational 2-division square criterion at these roots, their halves require respectively $\sqrt{-3}$, $\sqrt{-1}$, $\sqrt3$. Each quadratic field ramifies at 2 or 3, hence none is in $H_0$. Therefore $E_0(H_0)[8]=E_0[2]$ and the parenthesis is **one** rational 2-torsion point, not two unrelated local signs. In particular its reductions are equal at both places.

It follows from §2 that the 2-primary reductions of $B$ at $q_0$ and $p_\beta$ agree as elements of $E_0[2]$. In fact the full reductions are already in $E_0[2]$ by the previously checked quarter reduction argument: $2B_D$ has zero Kummer class, and its (a priori 2-torsion) reduction contributes precisely the corresponding injective torsion valuation parity since the remaining formal anti-invariant part has even parities. Thus both first Kummer valuation parities of $B_D$ at the two places are equal **to one another**. On the exact selected Selmer basis their difference is the mark coefficient, since all torsion has the same parity at each, $q_0\nmid\beta$, and $p_\beta\mid\beta$. Consequently there is a rational torsion $T$ with $B_D-T=2C_D$ on the actual twist. Multiplying by four kills $T$ and gives $P_D=8C_D$ over $\mathbf Q$.

This closes the earlier quarter-level CM−192 and reference-operator search as a marking producer for this selected family: whenever that narrower single-helper formula applies, its quartic residue is $+1$ for structural reasons. It holds on either actual selected detector arm satisfying the stated hypotheses, not on arbitrary scalar poles or weakly selected twists. It does not give exact coordinates, a rational marked eighth, positive or zero rank, or an obstruction to marked rationality by another producer. The surviving odd order reduction tests are unchanged by forced division by eight.

### Exact inputs

- The ramified full trace pairing and formal parity, *The raw level-48 Heegner trace is a rational double*, SHA-256 `59feb8a9913e701fb1c82116c15908858712899c0bc53dfc603e100db36ea430`.
- The exact actual fourth multiple, *The first half of the raw level-48 detector trace is unmarked*, SHA-256 `bbfe4e889f688bcf69f8b643fc60615fb0945ff0ab1862ff21e28127744535f3`.
- The precise quarter reduction rule, *The next detector saturation sign is an oriented CM intersection ideal*, SHA-256 `c83ce5b2c7d6c95283d67f375f3c306f8ed62ead52c344c78d33ba991724ae7e`.
- The same-map genus height ratio, *Exact ordinary genus divisibility and the normalized Heegner bit*, SHA-256 `62ef751c390e12d5903fe0741530c2a44bedf5b3eee83d31ffd2e27f3206487e`. It uses [Cai–Shu–Tian, Theorem 1.1](https://arxiv.org/pdf/1408.1733) and [Feng–Liu–Pan–Tian, Proposition 2.6(i)](https://arxiv.org/pdf/2405.11132).
