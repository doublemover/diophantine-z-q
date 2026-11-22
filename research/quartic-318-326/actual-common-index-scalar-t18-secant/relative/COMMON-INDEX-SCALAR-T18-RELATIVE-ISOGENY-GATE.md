# The common-index input-zero scalar needs one specific relative isogeny class

This concerns the actual **scalar** among the original simultaneous four-Ready poles, not an independently chosen old scalar. It uses the existing existential common index and its full scalar support-unit preparation, with no new prime key. The known free $t=18$ first curve scales at that actual scalar. The reviewed detector proof using its exact Selmer eight does **not** give the scalar's rational mark. There is instead a precise single relative isogeny obstruction to the raw scalar PointPair for this first choice. Nothing here evaluates it.

## 1. The same fixed first curve and mark at the actual common index

For input $a=0$, the exact native `ScalarForwardWitness318.poleInput` has
$$
 b=L_s\left(\frac{W}{1+L_s}\right)^2,\quad
 L_s=114444\cdot4376874610839020,\quad
 17L_s=204^2\beta,\quad\beta=204618888056724185.
$$
Hence for the **literal** $B=17b$ there are the exact identities
$$
 \rho=\frac{204W}{1+L_s},\qquad B=\beta\rho^2,\qquad
 c=\rho/17,\qquad \delta=1-b/17=1-\beta c^2.
$$
This holds for the retained new labels and eventual common index, regardless of whether $W$ agrees with its archived numerical value. The simultaneous handoff retains full scalar support-unit preparation. Thus $v_p(b)=v_p(L_s)>0$ at each $p\mid\beta$, with $v_{17}(b)=2$; and the prepared depths at 2 and 3 are $4,2$. It follows that $\delta$ is a square at $2,3$ and each prime of $\beta$, and is positive by $0<b<17$.

Set $t_*=18$, $A=1+3\beta t_*^2$, $k=(1-\beta t_*^2)(1-9\beta t_*^2)$, $n=\beta k$, and $F=E_n$. The already checked rational point
$$
 P=(\beta A^2,\ 8\beta^2 t_* A(1-3\beta t_*^2))
$$
has ordered Kummer class $(\beta,1)$ in the $(x,x-n)$ slots. This curve and $P$ depend on $\beta,t_*$ alone, which are unchanged. Scaling by $(\rho/A)^2,(\rho/A)^3$ gives the first point at $B$ on $E_T$ for $T=n(\rho/A)^2$, on the actual scalar. Put $d=n\delta$ and $\mathcal E=E_d$. Any rational point of this companion with $x=\beta v^2\ne0$ scales by $(B\rho/A)^2,(B\rho/A)^3$ to the desired second point: the parameter becomes $TB^2\delta$ and $x$ becomes $B(Bv/A)^2$. The native raw PointPair does not require a prescribed second Kummer slot.

The full class $(\beta,1)$ on $\mathcal E$ is everywhere locally admitted, without the archived ramified 6551 or 16782959 rows. At the square places of $\delta$ and at infinity this is the image of $P$. At an odd $p\ge5$ where $\beta$ is square the class is trivial. At every remaining $p$ the parameter has even valuation: $n$ is a unit because a zero of either factor of $k$ would make $\beta$ a square modulo $p$, and any negative depth of $1-\beta c^2$ is even, while odd positive depth would again make $\beta$ a square. The companion then has good reduction after local square scaling. Its full unramified unit pair subgroup occurs, since rational 2-torsion and the odd-residue formal group give local Kummer image of size four. Both slots are units as squareclasses, yielding the claimed admission. This does not transfer the old additional ramification constraints or its exact one-bit index to the new scalar.

## 2. The exact ordered relative class and its single raw image

If $\delta$ is square, the first point transfers to the companion directly. Otherwise put $K=\mathbb Q(\sqrt\delta)$ and let $j:\mathcal E_K\to F_K$ be the scalar twist isomorphism. Write $\sigma$ for the nontrivial automorphism of $K/\mathbb Q$ and $L$ for the everywhere-local trace subgroup of $F(\mathbb Q)$. Under $j$, the $\sigma$ action on $\mathcal E(K)$ is $-\sigma$ on $F(K)$. Consequently
$$
 H^1(\operatorname{Gal}(K/\mathbb Q),\mathcal E(K))
 = F(\mathbb Q)/\operatorname{Tr}_{K/\mathbb Q}F(K).
$$
Indeed an order-two cocycle's value becomes a $\sigma$-invariant point of $F(K)$, and an order-two coboundary becomes a negative trace. Galois inflation--restriction, globally and locally, then identifies
$$
 \ker\!\left(\Sha(\mathcal E/\mathbb Q)\longrightarrow\Sha(\mathcal E/K)\right)
 = L/\operatorname{Tr}_{K/\mathbb Q}F(K).
$$
At a split place the local trace is from the corresponding étale product and is onto. At a field place the same cocycle calculation applies. No finiteness of Sha is needed.

Let $\kappa$ be the image of the ordered class $(\beta,1)$ in $\Sha(\mathcal E/\mathbb Q)[2]$. It is precisely the above relative class labelled by $P$. For a check of sign, choose $U$ over $\overline{\mathbb Q}$ with $2U=P$. Under the identification of geometric 2-torsion by $j$, the class is represented by $gU-U$. Subtract the coboundary of $j^{-1}U$ in $\mathcal E$: after applying $j$, the difference is $(1-\chi_\delta(g))gU$, where $\chi_\delta$ is the quadratic character of $K$. It is zero on $G_K$, and equals $P$ on its other coset. This proves the exact relative label and the trace equivalence for the ordered class.

For the **raw** condition let $\phi:\mathcal E\to G$ be the zero-root 2-isogeny, with $G=E'_d$ and dual $\hat\phi$. The smaller specified class is
$$
 \kappa_x:=\phi_*(\kappa)\in
 \ker\!\left(\Sha(G/\mathbb Q)[\hat\phi]\longrightarrow\Sha(G/K)[\hat\phi]\right).
$$
The isogeny Kummer diagram for
$0\to\mathcal E[\phi]\to\mathcal E[2]\xrightarrow{\phi}G[\hat\phi]\to0$
maps the full Kummer class to its bare x-squareclass $\beta$. The ordinary connecting map for $\hat\phi$ is the x-squareclass map, and its image is the kernel of $H^1(\mathbb Q,G[\hat\phi])\to H^1(\mathbb Q,G)$. Thus $\kappa_x=0$ **if and only if** there is a rational bare x-class $\beta$ on this $\mathcal E$. As $\beta>0$ is nonsquare, neither the identity nor the zero-root torsion (class $-3$) can represent it. It necessarily gives the legitimate nonzero abscissa in the raw scaling above, even if it happens to be $(d,0)$. This proves equivalence to a raw scalar PointPair with this prescribed first choice. Vanishing of $\kappa$ also suffices, but it can be stronger than the raw need. Injectivity on the indicated relative $\hat\phi$-killed subgroup would suffice without the detector's Selmer-size assumption.

## 3. What transfers and what remains unproved

An equivalent bare arithmetic certificate avoiding a factorization of $\delta$ is one point
$$
 w^2=\beta(v^2-k\delta)(v^2+3k\delta),\quad v\ne0,
$$
since $(x,y)=(\beta v^2,\beta v w)$ on $\mathcal E$. For the ordered/trace variant, the exact compact norm $(1+c\sqrt\beta)(1+18\sqrt\beta)(1+54\sqrt\beta)$ supplies $v^2-\beta u^2=k\delta$, but the coupled $z^2=v^2+3k\delta$ still needs a rational solution. The fixed beta and dyadic pure-second matrix from the t18 support proof also survives: the required two-adic class of $d$ is square and the beta-place stripped tests are unchanged. Thus on any such scalar an independent second slot cannot be supported solely on the fixed factors of $n$. The additional two archive-specific Jacobi rows are not claimed at a new index.

There is a direct failed premise for transplanting the detector's 5-class rank theorem: **5 is always additive on this scalar companion.** In fact $5\mid\beta$ to odd depth, $k\equiv1\bmod5$, and $\delta$ is locally square. Square scaling to depth one gives the stock integral equation of discriminant depth six (hence minimal) and cuspidal reduction $y^2=x^3$. So 5 is not good ordinary. Independently, even if a rank-one result at another prime were supplied, its positive rank would not by itself imply that the *specified* x-class lies in the rational image. The exact detector argument fixes this using its known size-eight Selmer group; no such size is known for this scalar, and finiteness of Sha is not vanishing of the class above.

### Exact pins and limited scope

- The eventual simultaneous four-Ready/physical-anchor theorem and full scalar preparation, checksum-list `9dc74e33f8afb1fdb40aae98ed766ab5bedb8f8cb63b828c4bc04f401e9b34f5`. The native scalar formula is `ScalarForwardWitness318.lean`, source SHA `9b21f269bbf73da643a7259f71dc67ea835a52aaa97bbb6d449549004bf7038c`.
- Fixed $t_*=18$ first point, normalization and archived trace theorem, bound source list `16ba82294a3aeef50bfd7182c33ab01fa04a3e541238e2870be2901b3cdb312b`.
- Fixed t18 pure-second support calculation, checksum-list `66b5e1c5e01763abfbc6a060d5889621ee07580158a73c393017db091e5f27d3`.
- The separate exact detector five-class criterion and published source `8a20b6a4f42d9293c434c50dbcf24430417b78a9`.

No common index, factorization of the complement, relative Sha class value, scalar rank or companion point was computed. No new prime, parameter scan or changes to the source are used.
