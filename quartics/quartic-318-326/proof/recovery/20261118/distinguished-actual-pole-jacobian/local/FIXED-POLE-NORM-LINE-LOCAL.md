# A distinguished everywhere locally soluble curve in the unrestricted marked-pair test

Fix any one of the four actual prepared poles at a given common source index. Use its literal positive rational data
$$
  0<R=b/17=\beta u^2<1,\qquad D=1-R=\theta z^2
$$
with $u,z\ne0$ and positive squarefree $\beta,\theta$. (Here $u$ is the square scale for $b/17$, not $17b$.) We use only the following local preparation: at 2 and 3, and at each prime dividing $\beta\theta$, at least one of $\beta$ and $\theta$ is a local square. For the actual data, use $\beta$ at 2 and at primes of $\theta$, and $\theta$ at 3 and at primes of $\beta$. Non-square $\theta$ is the interesting case.

Consider the smooth projective genus-one curve with affine equation
$$
  C_R:\quad \beta d^2=(R\lambda^2-2\lambda+1)(R\lambda^2+6\lambda+9)=F(\lambda).
$$
**It has points over every completion of $\mathbb Q$ for every such pole.** This is about one fixed rational curve for that unchanged $b$, not independently adjusted gain parameters at different places. Its degree-two map to the $\lambda$-line has a rational divisor of degree two. In particular its class as a torsor under its Jacobian belongs to $\Sha[2]$ (possibly zero); the index divides two. This does not assert that every class in that group vanishes.

The two quadratics have discriminants $4D$ and $36D$. Their difference is $8(\lambda+1)$; they have a common zero only if $R=-3$. Hence for $0<R<1$ the four geometric branch points are simple and distinct, the cover is geometrically connected, and infinity is unbranched.

* Whenever $\beta$ is a square in the completion take $\lambda=0$, where $F=9$. If $\theta$ is a square then $D$ is one, and the first quadratic has a simple root, giving a smooth branch point. This includes infinity and handles all specified small or ramified places.
* It remains to treat $p\ge5$ with $\beta,\theta$ both nonsquare units. If $v_p(R)>0$, then $D\equiv1\pmod p$ is a square, impossible. If $v_p(R)=0$, neither $R\equiv1$ (since $R=\beta u^2$) nor $R\equiv-3$ (since then $D\equiv4$). Thus the quartic mod $p$ has unit leading coefficient, four distinct branch points, and good genus-one reduction.
* If $v_p(R)<0$, then $v_p(1/u)>0$. Change coordinate $l=u\lambda$. The reduction of the right side is $(\beta l^2+1)(\beta l^2+9)$; it again has four distinct simple roots, with none at infinity. The weighted projective double-cover model is smooth over $\mathbb Z_p$: equivalently use the affine chart just tested and its reciprocal chart with $d/l^2$, where the constant coefficient at infinity is a unit.

In the two good reduction cases, the Hasse bound gives a smooth point mod $p$, and Hensel lifting gives a local point. Any local point, even if at infinity or at a branch, has a smooth analytic neighborhood, so one can avoid the finitely many deleted parameters in the transformations below. No statement about simultaneous rational approximation on this genus-one curve is being used.

**The same curve in two recent formulations.** In the aligned full-mark quadratic norm criterion take $X=\lambda(1+z\sqrt\theta)$. Its first norm is $R\lambda^2$, and the product of its other two norms is exactly $F(\lambda)$. For a rational nonbranch affine point with $\lambda\ne0$ this gives the full aligned norm triple with some secondary mark, so a literal rational PointPair follows by the reviewed trace and scaling. In fact at $\theta>1$ a rational point on $C_R$ cannot be a branch (discriminant class $D$), nor at $\lambda=0$ or infinity ($\beta$ positive nonsquare, in fact having odd valuation at 17). Thus **any** rational point counts for the literal pair allowing zero ordinates; it does not by itself exclude zero ordinates.

Independently, in the unrestricted iff use $r=1/R=\beta (1/(\beta u))^2>1$. Its first quadric becomes $(b_1/z)^2=a^2+12r$. Set $a=\lambda-3r/\lambda$ and $b_1/z=\lambda+3r/\lambda$, which parametrizes that hyperbola off its points at infinity (conversely $\lambda=(a+b_1/z)/2\ne0$). The second quadric becomes
$$
r(s\lambda)^2=(\lambda^2+2r\lambda-3r)^2-16r(r-1)\lambda^2=r^2F(\lambda).
$$
Hence $d=s\lambda u$ satisfies $\beta d^2=F(\lambda)$ and the two smooth completions are birational over $\mathbb Q$. This distinguished fiber is sufficient, not claimed necessary: the unrestricted equivalence permits other rational $r=\beta c^2>1$. Local points, the degree-two divisor, or solutions at other poles do not imply a rational point on the distinguished fiber. No numerical computation of $\theta$ is needed to specify $C_R$ once $b$ and its first class are given. Mathematical argument only, not a Lean theorem.
