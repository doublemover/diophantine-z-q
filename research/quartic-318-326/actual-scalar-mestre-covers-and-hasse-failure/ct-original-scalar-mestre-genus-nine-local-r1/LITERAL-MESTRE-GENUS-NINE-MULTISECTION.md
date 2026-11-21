# A second, everywhere-local multisection of the unchanged scalar Kummer

Keep the literal original \(a=0,h=473592745039516333133760\) and the scalar from the [raw Kummer reduction](../ct-original-scalar-kummer-fiber-r1/ACTUAL-RAW-POINTPAIR-KUMMER-AND-SCALAR-FIBER.md): \(\beta=204618888056724185\), \(0<\mu=\beta c^2<1\), \(\delta=1-\mu>0\) nonsquare, and all the old local guards. This is independent of the [new genus-one marked multisection](../ct-original-scalar-mestre-marked-genus-one-r1/LITERAL-MESTRE-MARKED-MULTISECTION.md). It is everywhere local **without** assuming a squareclass norm for the unknown support of \(\delta\). No rational point is asserted.

## 1. Construction and exact map

On the ordinary split-cubic Kummer of \(E_\beta,E_{\beta\delta}\) choose different shifted roots \((0,-3\beta\delta)\). As in the [Mestre rational construction](https://arxiv.org/pdf/1902.02897), set the ordinate ratio to \(u^3\) and the ratio of the two shifted abscissae to \(u^2\). With \(q=\delta u^2\) the unreduced normalized x coordinates are
\[
 z=\frac{12q^2+3}{2+7q},\qquad z_2=-3+z/q.
\]
Indeed shifting at 0 gives the normalized cubic \(x^3+2x^2-3x\), and shifting at the other root gives \(x^3-7x^2+12x\); the cubic terms cancel and the remaining equality is \((2+7q)z=12q^2+3\). Now translate by the positive-root 2-torsion on **both** elliptic curves. The normalized x coordinates become
\[
 F(q)=\frac{3(q+1)(4q+3)}{(3q-1)(4q-1)},\qquad
 G(q)=-\frac{3(4q^2+1)}{(4q-1)(4q+3)}.
\]
To lift exactly to the raw Kummer we require
\[
 q=\delta u^2,\qquad t^2=\beta F(q),\qquad (t')^2=\beta G(q).        \tag{1}
\]
Let \(\mathcal C\) be the smooth projective curve with this function field. To verify the raw map explicitly, set
\[
 Z=u^3\left(\frac{z_2-1}{z-1}\right)^2,qquad
 W=\delta^2\frac{t'}{t}\, Z f_\beta(t'),\qquad
 f_\beta(X)=(X^2-\beta)(X^2+3\beta).
\]
Here the standard translation ordinate is \(y\mapsto-4n^2y/(x-n)^2\); hence Z is exactly the post-translation ratio. Alternatively one can check directly
\[
 \big[x_1(x_1-\beta)(x_1+3\beta)\big]
   = Z^2\big[x_2(x_2-\beta\delta)(x_2+3\beta\delta)\big]
\]
using \(x_1=\beta F(q)=t^2,x_2=\beta\delta G(q)=\delta(t')^2\). Dividing out gives \(W^2=\delta f_\beta(t)f_\beta(t')\) with the same actual \(\delta\). Thus any rational point in this open gives the original PointPair via the pinned raw inverse map.

In fact all rational points of \(\mathcal C\) would be useful here. Over the real field, both positive x forms require \(0<q<1/4\) except possibly the displayed endpoints. At \(q=0\), \(F=9,G=1\) and \(\beta\) is a rational nonsquare. At \(q=\infty\) the value \(G=-3/4\) is negative. At \(q=1/4\) one would need \(\delta\) square rationally (since \(q=\delta u^2\)), and \(q=1/3\) has \(G<0\). No other pole or zero of F or G is at positive q. Thus no rational boundary point supplies a spurious solution. In the useful interval both t and t' are finite nonzero and the new point would have both original ordinates nonzero.

## 2. Genus, good reduction and exact local solubility

Over the q-line F branches at \(-1,-3/4,1/3,1/4\); G branches at \(\pm i/2,-3/4,1/4\). Under \(q=\delta u^2\), each of these nonzero finite roots has two distinct preimages, and no new branch at u=0 or infinity. The two independent square roots of (1) each have eight branch points; their branch sets share four, so their product square root also has eight. In the degree-four cover of the u-line there are 12 distinct branch points, each with inertia of order two. Riemann–Hurwitz gives \(2g-2=-8+12\cdot2=16\), so \(g=9\).

The same branch description works over \(\mathbf Z_p\) when p is odd, \(p\notin\{3,5,13\}\), and \(\beta,\delta\) are units. The six distinct geometric q-values stay distinct: the only possible odd-prime collisions of \(-1,-3/4,1/3,1/4\) away from denominators are 5 and 13, and evaluations of \(4q^2+1\) at these roots have prime support only 2,3,5,13. They stay away from 0 and infinity. The cover then has smooth proper reduction. Locally at a branch, after discarding even powers of the local parameter, the normalization has one square root of a unit times that parameter and one square root of a unit (if both original roots branch, replace the second by their product). These give a smooth ramified quadratic coordinate followed by an étale quadratic equation since p is odd. Away from the branch the cover is étale. The relative normalization is proper as a finite cover of the projective line, including at infinity.

We use the following argument over the actual completions. Multiplying \(\delta\) by a local square merely rescales u; q and the target equations are unchanged.

* **The real place:** take any  \(q\in(0,1/4)\), so all three square conditions and all required nonvanishing hold over the reals.
* **Any p where \(\delta\) is square:** take q very near \(1/4\). Both F and G have simple poles, with \(F/G\to64\), a nonzero square. The local inverse function theorem applied to \(1/(\beta F)\) at its simple zero lets its value be any sufficiently small nonzero square. q remains in its required local squareclass by openness, and then the other x form is square too. This includes 2,3 and all primes dividing \(\beta\), by the old guards.
* **Odd v_p(δ):** outside the preceding cases these primes have \(p\ge7\), \(\mu\equiv1\pmod p\) and \(\beta\) a local square. A negative valuation of \(\delta\) outside \(\beta\) would be even, so odd depth here is positive. Take u sufficiently small nonzero; \(F(q)\to9,G(q)\to1\) are squares. No restriction on which unseen odd-depth primes occur.
* **Even depth, unit nonsquare class of \(\delta\), after scaling u:** if \(\beta\) is square, again use q sufficiently near zero. If \(-3\) is a nonsquare unit, take q sufficiently near \(-3/4\), of precisely the class of \(\delta\). Here F has a simple zero and G a simple pole, while \(FG\to9/64\) is a nonzero square. The same inverse-function argument applied to \(\beta F\) works, since the product of the two forms is always square in a sufficiently small punctured ball.
* **Other p with even depth:** both \(\beta\) and \(\delta\) now have nonsquare unit class and \(-3\) square. For \(p>324\) the preceding good reduction description applies, and \(p+1-18\sqrt p>0\). Hasse–Weil gives a point on the smooth reduction; Hensel lifts it, and smoothness permits a perturbation outside the finite exceptional set. Below this bound we do not assume good reduction at 13. The attached exact replay enumerates the **15** primes \(7\le p\le324\) outside \(\beta\) with \(\beta\) nonsquare mod p and \(-3\) square mod p. For each it gives a nonzero nonsquare residue q for which \(\beta F(q),\beta G(q)\) are nonzero squares and all numerators and denominators are units. Since the actual class of \(\delta\) here is nonsquare unit, q is in that squareclass. This directly lifts the square equations over \(\mathbf Q_p\), without requiring smooth whole-curve reduction at the exceptional 13.

All the local witnesses can therefore be chosen in the useful open of (1). This theorem is only about the literal **same** scalar, including the compact original unseen support; it supplies no rationality or weak approximation claim for \(\mathcal C\). The point search on \(\mathcal C\) is now a separate arithmetic problem without a preliminary norm test on \(\theta\).

Replay: `python3 -B replay_mestre_genus_nine.py | cmp - EXACT-GENUS-NINE-CONTROLS.json`. Exact integer finite-class coverage and rational identities only; no broad scan, local Lean or remote write.
