# A distinct marked genus-one multisection on the literal raw Kummer

This is a new sufficient certificate using the **same** `a=0,h=473592745039516333133760` scalar, not a replacement b or a rational point. Keep the compact `c` of the [fixed scalar](../ct-original-scalar-kummer-fiber-r1/ACTUAL-RAW-POINTPAIR-KUMMER-AND-SCALAR-FIBER.md), \(\beta=204618888056724185\), \(\mu=\beta c^2\), and \(0<\delta=1-\mu<1\) with nonsquare class \(\theta\). All the claims retain the literal \(\delta\), not its truncation at visible support.

## 1. Explicit multisection and back-map

The raw Kummer uses \(f(t)=(t^2-\beta)(t^2+3\beta)\) and \(W^2=\delta f(t)f(t')\). Map its quartics to the split cubics \(E_\beta,E_{\beta\delta}\), where \(E_n:y^2=x(x-n)(x+3n)\), using \(x_1=t^2,y_1=t v_1\) and \(x_2=\delta (t')^2,y_2=\delta t'v_2\) with \(v_1^2=f(t),v_2^2=\delta f(t')\). The usual Kummer of the split cubics uses the ordinate ratio \(y_1/y_2\); lifting to the original raw equation requires the two exact abscissa classes, not just a point on that usual Kummer.

Mimic the explicit [Mestre–Kuwata–Wang construction, Gvirtz §§1–2](https://arxiv.org/pdf/1902.02897) at the rational roots \(x_1=\beta,x_2=\beta\delta\), **without depressing the cubics**. Put \(q=\delta u^2\), use \(y_1/y_2=u^3\) and \(x_1-\beta=u^2(x_2-\beta\delta)\). After the leading cubic cancels, the remaining linear equation gives
\[
 x_1/\beta=(1-4q)/5,qquad x_2/(\beta\delta)=(1-4/q)/5 .
\]
For example in shifted coordinates the polynomial is \(z^3+5n z^2+4n^2 z\). Now translate only the first point by \((\beta,0)\), whose abscissa transformation is \(x\mapsto\beta(x+3\beta)/(x-\beta)\). The two required marks are exactly
\[
 t^2=\frac{\beta(q-4)}{q+1},\qquad (t')^2=\frac{\beta(q-4)}{5q}.
\]
They are both enforced by this single smooth genus-one curve \(\Gamma\), with projective coordinates \([u:A:B:T]\):
\[
 A^2=(\beta/5)(u^2-4T^2/\delta),\qquad 5B^2=u^2+T^2/\delta.                  \tag{1}
\]
Any rational point of (1) has \(T\ne0\) (at infinity it would require \(5\) square). Set \(T=1\). Then \(q>4\): equality would give \(\delta\) square; all values below four force \(A^2<0\). In particular \(u,A,B\ne0\). The exact raw point is
\[
 t=A/B,\qquad t'=A/u,\qquad W=\frac{4\beta^2 B(4q-1)}{u^2(q+1)}.
\]
Indeed
\[
 f(t)=-5\beta^2(4q-1)/(q+1)^2,\qquad
 f(t')=-16\beta^2(q+1)(4q-1)/(25q^2).
\]
Use \(5 B^2=(q+1)/\delta\) in \(W^2\) to verify the raw equation. This direct check does not rely on choices of geometric lifts in the cubic-pair construction. Both conic parameters are finite nonzero and hence the pinned reverse map yields actual \(s\ne0\) and two nonzero ordinates of the original PointPair.

## 2. Exact [2]-cover and the independent rank target

The two square roots in (1) have four distinct geometric branch points over the u-line, two for each, all simply ramified and no overlap. Riemann–Hurwitz for the degree-four cover gives genus one. In fact put \(d=\beta\delta\). There is the explicit degree-four map to
\[
 G_d:Y^2=X(X-4d)(X+d),\qquad
 X=\beta\delta^2 u^2,quad Y=5\beta\delta^3u A B .
\]
The other differences are \(X-4d=5\delta^2 A^2\) and \(X+d=5\beta\delta^2B^2\). Its generic deck group consists of the four even sign changes of \((u,A,B)\). The three nonidentity elements have no geometric fixed point: at \(T\ne0\) the two flipped coordinates could not both vanish by (1), and at \(T=0\) all three are nonzero. On a smooth genus-one curve a fixed-point-free involution must be translation by a nonzero 2-torsion point (an involution with a nonidentity group automorphism has a fixed point over the algebraic closure). The quotient is thus by the full 2-torsion. The descended identification of the Jacobian of \(\Gamma\) with \(G_d\) and its [2]-covering are also recorded directly by the **ordered** split Kummer mark
\[
                       ([\beta],[5],[5\beta])
\]
in root order \((0,4d,-d)\). Conversely, a rational finite point with that exact mark gives (1) by taking the three square roots at the same displayed scales. It is not a root or the identity: the first slot of the roots other than \(4d\) is negative, and the first slot at \(4d\) is \([d]\ne[\beta]\). There is no rational 4-torsion: a rational half of a non-largest root is excluded by a negative root difference, and a half of the largest root would make both \(4d\) and \(5d\) square, impossible. Consequently this mark is not rational torsion, and when it is known to lie in \(\mathrm{Sel}_2(G_d)\), \(\operatorname{rank}G_d=1\) together with \(\dim_{\mathbf F_2}\mathrm{Sel}_2(G_d)\le3\) would prove it rational. Neither premise is asserted.

By translation of the untwisted x-coordinate by 1, \(G_1\) is exactly \(y^2=x^3-7x-6\), [Cremona 40a1 / LMFDB 40.a2](https://www.lmfdb.org/EllipticCurve/Q/40/a/2). It has \(j=148176/25\), integral at 3, unlike the old fixed-lambda receiver \(j=2048/3\) or the old \(k=0\) Jacobian (\(v_3(j)=-2\) at the actual \(v_3(\mu)=2\)). Hence this curve is not even geometrically isogenous to either older target, by preservation of potential good reduction under isogeny.

There is an exact global sign without factoring \(\theta\). Replace d by its positive squarefree class \(d_0=\beta\theta\); the factors are coprime by the actual positive \(\mu\)-depth at \(\beta\). Then \(d_0\equiv1\pmod8\), \(5\mid d_0\) exactly once, and \(d_0\equiv1\pmod4\). The twist at 2 is trivial, so the local sign remains + from the listed 40a1 local data. The ramified quadratic twist of its split Steinberg representation at 5 has sign \((-1/5)=+\); at odd primes away from 5 the good-model twists have sign \((-1/p)\) only if p divides \(d_0\). Both assertions follow by the local epsilon-factor formulas (for ramified quadratic \(\chi\), \(\epsilon(\chi)^2=\chi(-1)\), with the positive unramified factors in the two-dimensional case; compare [Dokchitser–Dokchitser, local root formula](https://arxiv.org/abs/0906.1815)). The latter signs multiply to + as \(d_0/5\equiv1\pmod4\). Infinity contributes −. Therefore \(w(G_d)=-1\), not a rank computation or a marked generator.

## 3. All-place criterion is the single **literal** norm from \(\mathbf Q(\sqrt5)\)

At every place where \(\delta\) is square there is the exact point \(u=2/\sqrt\delta,A=0,B=1/\sqrt\delta,T=1\); it is smooth, and can be perturbed off the finite exceptional set. This covers \(2,3\) and every prime dividing \(\beta\) by the actual guards. At the real place take \(u>2/\sqrt\delta\).

At any other prime p, let \(\delta=p^{2k}\delta_0\) and simultaneously scale \((u,A,B)\) by \(p^k\) to use \(\delta_0\); arrange \(v_p(\delta_0)=0\) or 1. If zero, (1) has smooth genus-one reduction: the two quadratic branch pairs remain disjoint and simple, as \(p\notin\{2,5\}\), \(\beta\) remains a unit, and the difference of the two branch-square values is \(5/\delta_0\). Its projective reduction has an \(\mathbf F_p\)-point by Hasse and lifts. If \(v_p(\delta_0)=1\), \(\beta\) is a local square (old \(\mu=\beta c^2\equiv1\pmod p\)); indeed outside \(\beta\) a negative \(\delta\)-depth is even so an odd depth is positive. If \(v_p(u)\ge0\) both right-hand sides have odd valuation −1, impossible. The same parity excludes an infinity solution unless the coefficients required below are squares. If \(v_p(u)<0\), \(u^2\) dominates, and (1) works exactly when both \(\beta/5\) and 5 are square, equivalently \((5/p)=+1\). For sufficiency take u with arbitrarily negative valuation.

Thus \(\Gamma\) is everywhere locally soluble iff **every odd-depth prime of the literal \(\delta\) splits \(\sqrt5\)**. This is equivalent to \(\delta\) being a rational norm from \(\mathbf Q(\sqrt5)\): at odd unramified inert primes, norms have even valuations and all units are norms; at the ramified 5-place and at 2 the verified class is a square; the extension splits at the real place. Apply the Hasse–Minkowski theorem to the norm conic for the converse. All four already proved odd-depth primes \(131,6551,2470991,16782959\) split \(\sqrt5\), but **some further odd-depth prime exists and is untested**. A norm certificate would prove local solubility of this new marked curve, not global solubility. The exact cubic mark or rational point in (1) remains the new endpoint.

Replay: `python3 -B replay_mestre_marked.py | cmp - EXACT-MESTRE-MARKED-CONTROLS.json`. No broad scan, native Lean build, or remote write.
