# A prescribed signed simple collision at 5 on the actual first detector arm

Fix the actual balanced Selmer-eight selector with the first split $u=1,v=	heta$ and retain all its literal inputs, its helpers, and the permitted shared final-prime progression. Thus
$$
 n=Hq_0,\qquad H=17(eta/17)\prod I_i,\qquad q_0\equiv7\pmod{24};
$$
every prime in $H/17$ is $1\bmod24$, and $H$ is squarefree. All other original detector parameters remain as selected. There is no move to an auxiliary scalar equation or a substituted pole.

**Additional compatibility at 5.** The existing final-prime progression admits a unit residue $q_\ast$ at 5 such that $-Hq_\ast$ is nonsquare modulo 5. In particular this holds whenever 5 is outside the fixed companion support and the other old final-prime constraints: the linear-q actual $\beta$ does not contain 5, the helpers can be chosen away from 5, and then a new residue modulo 5 is independent. If the old progression already constrains 5, the stated nonsquare condition is a genuine prerequisite, not asserted automatic.

Then for either fixed $X$-flag in the actual fibre over $T=(3+2\sqrt3,2(3+2\sqrt3))$, either chosen level arm at 2 and 3, and either genus sign, there are infinitely many allowed shared final primes yielding a **single genuine term** at 5 with that sign and intersection length one. Fix the named local roots consistently as specified below. The conclusion is about individual terms, not their signed sum at 5, and gives no point or rank.

## 1. Exact smooth local prescriptions

Use the literal reduction and the exact p=5 constants of the receiver calibration. On the selected flag, transport via the degree-eight isogeny from $B:y^2=x^3+1$. With Frobenius $\pi$ and $v=4\sqrt{-3}$, use
$$
 u=kv+\gamma\pi,\quad \gamma=a+b\omega\in O_{K_0},\quad
 Q(k,a,b)=48k^2+5(a^2+ab+b^2).
$$
This gives $u^2=-Q(k,a,b)$, with at most powers of 2 in any endomorphism denominator after transport. The aim is $Q(k,a,b)=Hq_0$. Enlarge the rational progression modulus $M$ so it contains 5, all prime factors of $H$, and $24$, without changing the old bits; choose a single unit class $q_\ast\bmod M$ obeying the new nonsquare condition. Increase $M$, prescribing a compatible lift of $q_\ast$ if necessary, to lock the two eigenvalues at 2 and 3. Put $n_\ast=Hq_\ast$ locally. The modulus for selecting the vector $(k,a,b)$ at primes dividing $HM$ can be taken larger than $HM$ in what follows.

* **At 2.** Choose $k=0$ locally. In the selected flag the exact semilinear unit $\eta$ has norm $-5$ over the unramified quadratic 2-adic field. Choose $\gamma=(1-2r_2)/\eta$, where $r_2=(1\pm\sqrt{-n_\ast})/2\in\mathbf Z_2$ is the chosen level root. This is integral, has $N(\gamma)=n_\ast/5$, and the exact flag congruences give eigenvalue $r_2\bmod16$. A sufficiently deep congruence on the vector preserves these finite conditions and $Q\equiv n_\ast$ to the desired depth. In particular this works for either dyadic root, not just an unspecified level.
* **At 3.** As $n_\ast\equiv2\bmod3$, choose $a-b$ equal to $2r_3-1\bmod3$ for the selected root $r_3\in\{0,1\}$. Then $Q\equiv5(a-b)^2\equiv n_\ast\bmod3$, and the norm has nonzero derivative at this residue. Hensel-lift to any prescribed precision. Here $r_3$ is the level root, not the named residue of $\sqrt3$ at 5.
* **At 5.** Since the required $n_\ast\bmod5$ is 2 or 3, $48k^2=n_\ast\bmod5$ has two nonzero roots. Select the one for which $4ks$ is the named residue of $\sqrt D$ (where $s=\sqrt3/2$ in that residue field; select $\sqrt{17}=s$ to use the displayed spin convention). Choose any $\gamma\not\equiv0\bmod5$. The derivative $96k$ is a unit, so varying $k$ through its residue lifts $Q=n_\ast$ with this $\gamma$ kept fixed. This forces $v_5(n-48k^2)=1$ for the eventual integer solution. The locally named roots are compatible: $\sqrt3,\sqrt{17}$ generate a biquadratic field of which both have the same nonsquare class modulo 5, so choose the prime with $\sqrt3/\sqrt{17}=2$; the sign of the named $\sqrt D$ can be chosen independently by the embedding of $L=\mathbf Q(\sqrt D,\sqrt3,\sqrt{17})$. No global square-root sign is changed after that place has been fixed.
* **At 17.** Choose a nonzero isotropic vector for $Q\bmod17$. This ternary form is nondegenerate and contains a hyperbolic plane over the finite field, so such a vector exists and is smooth. It induces a nonzero nilpotent on $B[17]$: in the basis of the calibration the map from $(k,a,b)$ to three independent trace-zero coordinates has matrix with rows $(-4,2,-2),(8,2,4),(-8,4,2)$ and determinant $-144$, a unit at 17. The two calibration spin expressions cannot both give a zero Weil exponent. Scaling this vector by any nonsquare of $\mathbf F_{17}^\times$ changes the spin sign, preserves the isotropic condition and keeps a unit derivative. Select the desired sign, and lift $Q=n_\ast$ to precision surpassing depth one at 17. An actual embedding obtained this way has fundamental discriminant at 17, with valuation exactly one.
* **At any other prime of $HM$.** A nondegenerate ternary form over a field of odd order is isotropic; one hyperbolic plane represents every residue by a vector with nonzero derivative, including zero (use a nonzero isotropic vector). Thus choose and lift a smooth solution for the required value. No norm or quadratic character condition in the old progression is dropped here.

By CRT choose a nonzero integer vector $V$ satisfying all these conditions and $Q(V)\equiv Hq_\ast\pmod {HM}$. The relevant conditions on the vector itself persist modulo some integer $M'$; enlarge $M'$ to a multiple of $M$. In particular $A=Q(V)/H$ is a positive integer and is prime to $M$. We may arrange $\gcd(A,M')=1$ by keeping only the same support on $M'$; the local prescriptions raise exponents, not the prime set.

## 2. Prime production with the vector congruence intact

Choose an integer vector $W$ independent of $V$ such that $Q(W)$ is nonzero modulo every prime divisor of $A$. All those primes lie outside $2,3,5$ and outside $H$, so the choice is possible by CRT and nondegeneracy. The binary form
$$
 F(X,Y)=Q(VX+HWY)/H
       =AX^2+BXY+CY^2
$$
is integral, positive definite and primitive: $C=HQ(W)$ is prime to $A$ by construction. We need infinitely many rational primes $F(X,Y)$ with $X\equiv1,Y\equiv0\pmod {M'}$. The following elementary ray class argument keeps these **coordinate** congruences, rather than just the represented prime's rational residue.

Let $\Delta=B^2-4AC<0$, $J=\mathbf Q(\sqrt\Delta)$, $O$ the quadratic order of discriminant $\Delta$ and $f$ its conductor. The standard primitive-form correspondence gives the proper invertible ideal $\mathfrak a=(A,(B+\sqrt\Delta)/2)$ of norm $A$, with
$$
 \frac{N(AX+(B+\sqrt\Delta)Y/2)}{A}=F(X,Y).
$$
Put $\mathfrak b=A\mathfrak a^{-1}$, an invertible integral ideal that is the unit ideal locally over $M'$. By weak approximation in $J$, multiply $\mathfrak b$ by some $\lambda\in J^\times$ to make $\mathfrak b'=\lambda\mathfrak b$ the unit ideal locally over $f$, while making $\lambda\equiv1\bmod M'O$ locally at the primes of $M'$. At overlaps the two conditions agree since the original ideal is already the unit ideal there. More explicitly choose local inverses to its generators at $p\mid f,\ p\nmid M'$ up to local order units, and approximate 1 to precision $M'f$ at primes of $M'$. Extend $\mathfrak b'$ to the maximal order. Its ray class modulo $M'f$ contains infinitely many degree-one prime ideals, by ray class reciprocity and Chebotarev (degree greater than one has negligible prime count). This is the usual [binary form/prime ideal correspondence and ring class reciprocity](https://www.math.toronto.edu/~ila/Cox-Primes_of_the_form_x2%2Bny2.pdf), applied in the larger ray group to keep the coordinates.

For such a prime, prime to $M'f$, its order ideal is $\mathfrak p=(r)\mathfrak b'$, where $r\equiv1\bmod M'f$ locally in the maximal order at the modulus. This equality descends to the order at conductor primes since $r$ is an order unit there, and off the conductor by equality of orders. Hence $\alpha=Ar\lambda$ satisfies $(\alpha)=\mathfrak p\mathfrak a\subset\mathfrak a$ and $\alpha\equiv A\bmod M'\mathfrak a$ (at primes of $M'$ both $\lambda$ and $r$ are 1 modulo $M'O$). Writing $\alpha=AX+(B+\sqrt\Delta)Y/2$ now gives exactly $X\equiv1,Y\equiv0\bmod M'$ and $F(X,Y)=N(\mathfrak p)$ a rational prime. Choose it as $q_0$. It follows that the integer vector $VX+HWY$ keeps all local prescriptions and the prime belongs to all the old literal rows. Finitely many exceptional or forbidden primes can be discarded.

## 3. What is certified, and what is not

The resulting $u$ is integral at 2 by the exact eigenvalue test; away from 2 it is integral by construction. Since $v(1+u)/2=(1-u)v/2-48k$, the action preserves the literal cyclic 48-level, and its two eigenvalues identify the actual chosen subgroup arm. The new $D=-Hq_0$ is fundamental, so the embedding is optimal. The specified tangent root at 5 is precisely the inert-place normalization in the Deuring correspondence; thus this is an actual index of the selected CM orbit. The genus sign is the prescribed mod-17 bit in the p=5 evaluator. The exact unramified intersection depth formula gives length one at this index. Both Selmer eights/marks remain because the same original common final-prime progression is kept.

Choosing the other genus sign or other marked $X$-flag applies the construction again; it need not produce the same primes. No difference of the two **total** counts is obtained. In particular this does not produce an odd order of a signed ideal or establish a rational point.
