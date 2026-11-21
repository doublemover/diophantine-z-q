# The raw level-48 Heegner trace is a rational double on the selected detector twists

This conclusion concerns the **same** unweighted, oriented level-48 class trace used in the exact 13/19 test. It uses the genuine balanced 2-Selmer eights but no assumed rank, analytic-rank converse, nonzero phase, or rational point beyond the trace supplied by complex multiplication. It does not give coordinates of that trace, guarantee its first half is marked, or assert anything for an arbitrary Ready twist.

## 1. Selected hypotheses and the precise trace

Fix one original positive linear-$q$ detector $b$ and its $\beta=[17b]$. In particular $17\mid\beta$ and at least one genuine odd prime $p_\beta\ne17$ divides $\beta$. In this profile $\beta$ has six distinct genuine contact/denominator primes in addition to 17. Fix one balanced selected twist $n$ with prime-to-$6$ squarefree $n>0$, $n\equiv23\bmod24$, $\beta\mid n$, and its fresh selected prime $q_0\mid n$, $q_0\nmid\beta$. Both separate members of the actual paired selector meet these hypotheses after the original $q_0\bmod24$ refinement. Write
$$
E_n:y^2=x(x-n)(x+3n),\quad
 E_0:y^2=x(x+1)(x-3),\quad
 D=-n,\quad K=\mathbf Q(\sqrt D).
$$
Here $D$ is fundamental, 2 and 3 split in $K$, and $H/K$ is its Hilbert class field. On $X_0(48)$ take one chosen actual orientation $\mathfrak n=\mathfrak p_2^4\mathfrak p_3$ and the **full** class orbit $(x_\mathfrak a)_{\mathfrak a\in\mathrm{Cl}(K)}$ with this level ideal. Use the exact raw modular map $\phi$ of the fixed certificate, with
$$
\phi w_{48}=T_3-\phi,\qquad T_3=(3,0)\in E_0[2],\qquad
P=\sum_\mathfrak a\phi(x_\mathfrak a).
$$
No averaging or factor of two is introduced here.

The class number $h$ is divisible by four. Indeed the ramified prime ideals at 17 and at any genuine prime $p_\beta$ have order dividing two. Neither and not their product is principal: a generator of norm $17,p_\beta$, or $17p_\beta$ cannot be rational since these values are nonsquares, and a nonrational integer of $K$ has norm at least $n/4>17p_\beta$ from the norm form of $(a+c\sqrt D)/2$. The strict inequality follows already from the other genuine primes in $n$. The two ramified classes generate a subgroup of size four. By the exact complex-conjugation formula $cP=hT_3-P$, the raw $P$ itself is anti-invariant. Let $P_D\in E_n(\mathbf Q)$ denote its twist descent, with coordinates $(Dx,D\sqrt D\,y)$ before any further division.

## 2. Ramified reduction vanishes at every $p\mid n$ other than 17

Fix a rational $p\mid n$ with $p\ne17$. The base $X_0(48)$ and $E_0$ have good reduction there. Choose one prime of $H$ above $p$. Since $p$ is ramified in $K$ and $H/K$ is unramified, the inertia group in $H/\mathbf Q$ has order two and maps onto $\mathrm{Gal}(K/\mathbf Q)$. Write its nontrivial element as $\tau_p=r c$ with $r\in\mathrm{Gal}(H/K)$ and $c$ ordinary complex conjugation. By the class-orbit CM action and the exact level reversal, on the orbit
$$
\tau_p x_\mathfrak a=w_{48}x_{B\mathfrak a^{-1}}
$$
for one class $B$ equal to the level-ideal class times the class of $r$ (possible inverses depend on the Artin convention). Such inverses are irrelevant to the following quadratic character; no relation of individual points lacking its index is assumed.

The real genus field $\mathbf Q(\sqrt{17})$ is in $H$. In fact $17$ and $D/17$ are coprime fundamental discriminants, and the biquadratic field $K(\sqrt{17})$ has absolute discriminant $D^2$, giving no finite ramification over $K$. Let $\chi_{17}$ denote its quadratic class-group character. Both $\tau_p$ (inertia at $p\ne17$) and $c$ (real subfield) act trivially on $\mathbf Q(\sqrt{17})$. Thus $\chi_{17}(r)=+1$, whereas
$$
\chi_{17}(\mathfrak n)=\left(\frac{17}{2}\right)^4\left(\frac{17}{3}\right)=-1 .
$$
Therefore $\chi_{17}(B)=-1$ and the involution $\mathfrak a\mapsto B\mathfrak a^{-1}$ has no fixed class, since a fixed class would square to $B$. This pairs characteristic-zero indices, so collisions upon reduction do not affect the pair count.

Inertia does not change the reductions. Thus at each paired contribution $\overline{x}_\mathfrak a=w_{48}\overline{x}_{B\mathfrak a^{-1}}$, so the sum of its two $\phi$-values is $T_3$. The aggregate trace is $(h/2)T_3=O$ in the residue field. This proves
$$
\overline P=O\quad\text{at every }p\mid n,\ p\ne17.
$$
The proof **does not** claim the same inertia-character formula at $17$: inertia may act nontrivially on the chosen real genus field there. No assertion about its fixed-class set is needed below.

## 3. Two of these reductions force the rational Kummer class to be trivial

At any such $p$, if $P\ne O$ its formal parameter $z=-x/y$ at $O$ in $E_0(K_p)$ is nonzero, of positive valuation, and satisfies $c(z)=-z$. Hence $z=\sqrt D\,u$ with $u\in\mathbf Q_p$, and its valuation in the ramified quadratic extension (normalized by $v_{K_p}(\sqrt D)=1$) is odd. The formal expansion $x=z^{-2}+\text{integral terms}$ implies that for any integral root $e=0,-1,3$
$$
v_p\big(D(x-e)\big)=1-v_{K_p}(z)\quad\text{is even}.
$$
The expression lies in $\mathbf Q_p$ since $c(x)=x$. In particular the two Kummer coordinates of $P_D$, ordered as $(x_D+3n,x_D-n)$, have valuation parity $(0,0)$. At $P=O$ the same statement is immediate.

The actual global 2-Selmer group has size eight and contains the marked class $M=(\beta,1)$ in this order. The rational $2$-torsion contributes its four classes
$$
(1,1),\quad (3n,-n),\quad(n,1),\quad(3,-n).
$$
At any odd $p\mid n$ these have distinct valuation pairs $(0,0),(1,1),(1,0),(0,1)$ respectively. Since $q_0$ is fresh and $\beta$ is a unit there, $M$ has parity zero at $q_0$ and at the same time it is nontrivial (e.g. parity $(1,0)$ at $p_\beta$). It is therefore outside the torsion image, and the whole Selmer group is the direct sum of this two-dimensional torsion image and the line generated by $M$. This does not assume that the mark has a rational representative.

Apply this decomposition to the rational class $\kappa(P_D)$ inside Selmer. The zero parity at $q_0$ kills its torsion component, since the mark has zero parity there and the torsion parities are injective. The zero parity at $p_\beta$ then kills the remaining mark coefficient (the mark has nonzero parity there). Both these primes differ from 17. Consequently $\kappa(P_D)=0$, and the Kummer kernel is exactly $2E_n(\mathbf Q)$:
$$
\boxed{P_D\in 2E_n(\mathbf Q).}
$$
This holds independently of whether the small-prime 13/19 phase is zero. Conversely, using only the ramified-prime conclusion and the same two supports, no translate of the undivided $P_D$ by rational torsion can be the literal mark: at $q_0$ the translate would require zero torsion parity and thus no translate, after which it fails at $p_\beta$. This last obstruction to direct marking does not use Selmer size eight; the rational-double conclusion does.

## 4. What two-division can and cannot produce

If an order-three receiver gives a nonzero value, the existing argument makes $P_D$ nontorsion and the exact Selmer eight gives rank one. The new rational-double identity guarantees a first halving over $\mathbf Q$ with no torsion correction. It does not say that this first half is already marked or that any particular further halving works. To construct the desired mark **given exact rational coordinates of the trace**, one can saturate under two-division up to rational torsion as follows.

At each step, test the point's Kummer class against the four rational torsion classes. If it lies in that image, subtract the matching actual $2$-torsion point and choose a rational half, using e.g. the ordinary split-root halving formula (equivalently, solve the explicit finite multiplication-by-two equations with the certified squareclass). On a nontorsion point this stops: modulo the finite torsion group each step divides the nonzero integral free coordinate by two. At termination the non-torsion Kummer coset is the unique coset $M+$ torsion, so subtract the specific rational torsion class required to produce $M$. This is an exact rational procedure when the characteristic-zero point is supplied. The actual rational torsion here is $C_2^2$ (the exact split Tate bound at 3, or the two genuine ramified-prime argument in the fixed certificate).

In contrast, a residue phase only certifies nonzero rank; it does not supply rational coordinates to perform any of those halvings. Multiplication by two is a unit for the order-three readout, so the forced divisibility neither makes that phase vanish nor computes a primitive coefficient. There is no evaluated phase, certified numeric source, or marked point in this packet.

### Exact source pins and small algebra replay

- *A fixed-level finite Heegner certificate for the actual balanced detector pair*, SHA-256 f1ffe375bf6fe92afe707d06f88dfc6bef2bb2da80532f48cc939f65e395104c, for the full oriented orbit, raw $\phi$, $T_3$ sign, twist descent and torsion. 
- *A shared final prime retains the two Selmer eights under a detector split*, SHA-256 4b2d39bf6b4f5e9dda8e33482c723dfba02569f8a0e285c005c646aa35d5fe6e, for the literal membership, size and the fresh $q_0$.
- *Actual 13/19 order-three coefficient contract*, SHA-256 2b67bc37a0e5514d6acbc977094035a862249f33a42bea6c6cb085591706ac0e, for the compatible positive-only rank certificate.

The associated finite replay verifies the exact stacked parity matrix and that its only zero class is the identity; it evaluates no CM trace or example pole.

    python3 -B replay_ramified_kummer_saturation.py | cmp - EXACT-RAMIFIED-KUMMER-SATURATION.json
    sha256sum -c SHA256SUMS
