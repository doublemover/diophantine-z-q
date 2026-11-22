# D = −311 control: the 11 projection is not principal; 19 takes a bounded candidate test

The complete oriented 11 calculation for the bounded fixed-241 control already has both coefficient places and their complex conjugates. This note uses that exact data to prove an **actual order-13 obstruction to settling 11 by itself** and identifies a least remaining rational prime candidate in the compact support sieve. It does not compute a single marked valuation at 19, the whole control ideal, or any original detector arithmetic.

## 1. The known projected valuation cannot settle as a principal ideal

Use the exact independently authenticated 11-projection record with manifest `c73012e9c6c2e17cbebd33d604e46f017b7e27f23f6e111962b67262b3586017`. The three projections to $M_1,M_6,M_{30}$ vanish at 11. In

$$M_5=\mathbb Q(\sqrt{-374755}),\qquad \omega=(1+\sqrt{-374755})/2,$$

the projected ideal supported at 11 is exactly

$$J_{11}=\mathfrak p^{-80}\bar{\mathfrak p}^{80},\qquad \mathfrak p=(11,\omega-5).$$

Indeed the incoming named radical roots at 11 are 9 and 2, hence the square-integral-generator residues are 5 and 7. The orientations are not chosen anew. At the output place over 29, the same radical is $8s$ for $s^2=2$: it is the named product $18(-6s)$.

Exact binary ideal multiplication and Gauss reduction show $\mathfrak p^{26}$ principal but $\mathfrak p^2$ and $\mathfrak p^{13}$ nonprincipal. For the principal power, an actual generator is $15409847948600+100845523307\omega$ or its negative, with exact norm $11^{26}$ and the exact HNF of $\mathfrak p^{26}$. The two proper powers give nonunit reduced ideals. If an input ideal were principal, exact shortest-vector normalization in its imaginary quadratic field would return the unit reduced ideal; hence these nonunit results certify nonprincipality rather than just a failure to find a unit. Since the prime's order divides 26, these two tests establish exact class order 26.

It follows that $[J_{11}]=[\mathfrak p]^{-160}$ has **order 13**. The independently reduced HNF is $\langle245,177+\omega\rangle$. The tracked residue used for ideal composition is not a generator phase of this nonprincipal ideal. At least one rational prime other than 11 must therefore contribute to the full oriented $M_5$ ideal, whose known construction is principal. The complete 11 valuation alone cannot give even this binary field's principal cubic readout.

## 2. The first other rational prime candidate can be made explicit

Exceptional 2,3,5,7 and ramified target places are already excluded by the separate exact interface for this regular control. At 13 the moving CM field splits, so no good-prime collision with the different fixed $K_*=\mathbb Q(\sqrt{-5})$ is possible. At 17 the projected imaginary field $M_5$ is nonsplit; inverse conjugation makes its oriented exponent zero. At 19 both moving and auxiliary CM fields are inert, whereas $M_5$ splits. Take $s^2=2$ in characteristic 19 and the following coherent names:

$$\sqrt D=5s,\quad \sqrt{241}=4s,\quad \sqrt{-74951}=2,
   \quad \sqrt{-5}=8s,\quad \sqrt5=9,\quad \sqrt6=5.$$

The named $M_5$ radical is $-1$ and gives the prime $\mathfrak q=(19,\omega)$; the opposite radical is $1$. Exact binary reduction gives $\operatorname{ord}[\mathfrak q]=26$ (the same proper-power test; the principal power has verified norm $19^{26}$). Moreover $J_{11}\mathfrak q^6\bar{\mathfrak q}^{-6}$ is principal. Thus **if** 19 were the only other contributing rational prime in this projection, its named exponent would have to be $6\bmod13$. This is a constraint and feasibility witness in the projected class group, not an assertion of that valuation.

There are also explicit good-prime collision-shell candidates at 19 spanning both exact auxiliary 16 modes, with $M=241,D_A=-320$ and $m=M^2 D D_A-x^2$:

| $x$ | $x\bmod32$ | $m$ | $v_{19}(m)$ | Exact off-diagonal numerator $(a,b)$ |
|---:|---:|---:|---:|---:|
|112|16|5780208576|1|(3110,1679)|
|1024|0|5779172544|1|(2215,1942)|

Both satisfy $x\equiv17\bmod19$, the named trace demand $x\equiv (M\sqrt D)\sqrt{D_A}\bmod19$ with $\sqrt{D_A}=8\sqrt{-5}$. In the rational quaternion algebra $B_{19,\infty}=(-5,-19)$, put $u^2=-5$, $J^2=-19$, $Ju=-uJ$, and $U=8u$. The presentation is ramified precisely at 19 and infinity: the symbols at 2 and 5 are positive by the odd-unit formula and $-19\equiv1\bmod5$, and other odd finite places outside 19 see both units. The explicit candidates are

$$W=(x/D_A)U + (a+bu)J/5.$$

The replay checks $a^2+5b^2=25m/(320\cdot19)$, hence $W^2=M^2 D$ exactly. They are integral in the unramified/differential $19$-adic maximal order because all displayed denominators are units there, and they have the exact required odd depth. This goes beyond a Legendre-only support row, but **does not** place $W$ in the fixed actual geometric order globally or establish the literal 16/3/241 flags. Such a marked candidate, and the whole signed sum at 19, remain to be computed. The order-13 argument proves only that some other prime is needed, not that 19 is that prime.

The exact script binds the complete 11 projection and the already checked compact ideal machinery. It supplies no further information about an original selected detector.

```sh
sha256sum -c SHA256SUMS
python3 check_D311_p11_order13_p19_candidate.py | cmp - EXACT-D311-ORDER13-AND-P19.json
```
