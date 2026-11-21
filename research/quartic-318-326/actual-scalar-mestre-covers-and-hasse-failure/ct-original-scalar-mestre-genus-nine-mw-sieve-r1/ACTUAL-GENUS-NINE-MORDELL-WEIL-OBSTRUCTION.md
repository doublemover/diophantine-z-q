# The actual genus-nine multisection has no rational point

This closes the new [everywhere-local genus-nine multisection](../ct-original-scalar-mestre-genus-nine-local-r1/LITERAL-MESTRE-GENUS-NINE-MULTISECTION.md), on the same original compact scalar, by a two-prime rational Mordell–Weil obstruction. It does **not** obstruct the raw Kummer surface away from this multisection, the separate genus-one multisection, or the fixed-lambda fibre. The previous all-place proof for the genus-nine curve remains valid.

Retain the actual \(\beta=204618888056724185\), \(\delta=1-\beta c^2\), \(q=\delta u^2\), and both square equations \(t^2=\beta F(q),(t')^2=\beta G(q)\) in the referenced multisection. We use only two verified local source facts: \(v_{17}(\beta)=1\) and \(\delta\in\mathbf Q_{17}^{\times2}\) is a unit, and at 131 the actual \(v_{131}(\delta)=1\), \(\beta\) is a square unit, \(-3\) is a nonsquare unit. At 17, \(v_{17}(\mu)=1\) on the literal scalar, so \(\delta\equiv1\bmod17\). At 131 the [exact original source replay and independent materialized-scalar check](../ct-original-scalar-raw-kummer-mobius-boundary-r1/ORIGINAL-RAW-KUMMER-EXACT-NORM-BRANCH.md) give \(\delta\equiv82\cdot131\bmod131^2\), not an artificial replacement for \(\delta\).

## 1. Project to the fixed ratio elliptic curve

All rational points on the genus-nine multisection would be in its useful affine open \(0<q<1/4\), by its actual real and boundary analysis. In particular t,t' are nonzero. The ratio square imposes
\[
 s^2=-(q+1)(3q-1)(4q^2+1),\quad
 s=\frac{t}{t'}\,\frac{(3q-1)(4q^2+1)}{4q+3}.
\]
Then
\[
      x=20/(q+1)-15,\qquad y=20s/(q+1)^2
\]
is a rational point \(R\) on the same small fixed curve \(E_*:y^2=x(x^2-2x+65)\). To see the identity, set \(z=1/(q+1)\); then \((s z^2)^2=(4z-3)(5z^2-8z+4)\), which becomes the equation by \(x=20z-15\), \(y=20s z^2\).

## 2. Exact rank one and odd index of the specific P

Let \(P=(5,20)\) and \(T=(0,0)\) on \(E_*\). The standard two-isogeny descent for \(y^2=x(x^2+a x+b)\) has the x-squareclass homomorphism \(\alpha\), with \(\alpha(T)=[b]\), and the dual curve \(y^2=x(x^2-2a x+(a^2-4b))\). We use the exact Tate rank formula \(2^{r+2}=|\alpha(E_*)|\,|\alpha(E_*')|\) (Silverman–Tate, *Rational Points on Elliptic Curves*, III.6; see also [AEC two-isogeny descent](https://www.math.ens.psl.eu/~obenoist/refs/Silverman.pdf)). The image consists of squareclasses supported on signed divisors of b; at p not dividing b both negative and positive x-valuations are even by comparing the unique leading or constant term in the quadratic. The homomorphism and formula concern actual rational points, not an assumption on any Sha group.

On \(E_*\) x is nonnegative at real points since \(x^2-2x+65=(x-1)^2+64\). The only possibilities are \(1,5,13,65\); both \([5]\) and \([65]\) are realized by P and T, so all four occur.

The isogenous curve has \(a'=4,b'=-256\). Its only possible classes are \(\pm1,\pm2\); \(-1\) is realized by its T. Class 2 is impossible already over \(\mathbf Q_2\). Indeed taking \(x=2(U/V)^2\) and multiplying by the denominator gives the necessary equation
\[
 N^2=2U^4+4U^2V^2-128V^4,
\]
with \(U,V\) primitive in \(\mathbf Z_2\). If U is odd the valuation is 1. If U is even, write \(U=2k\) and V is odd; the required square after dividing by 16 is \(2k^4+k^2V^2-8V^4\). For odd k this is 3 modulo 8. Otherwise put \(k=2l\) and divide out its square factor 4, to obtain \(8l^4+l^2V^2-2V^4\), which is 7 modulo 8 for odd l, and 6 or 2 for even l. All cases fail. Class -2 is also impossible by multiplying by the realized class -1. Thus the dual image has size two, and the Tate formula gives rank one exactly.

The discriminant of the written model is \(-2^{12}5^2 13^2\). At the good reductions 3 and 11 the exact point counts are 6 and 10. Prime-to-residue-characteristic rational torsion injects under reduction; using both primes rules out all odd torsion and makes the 2-part order at most 2. Thus the torsion is precisely \(\langle T\rangle\). Finally P's free index m is **odd**: if \(P=2kG+eT\) for a free generator G, its x-squareclass could only be 1 or 65, not 5. Consequently for any R there are integers n and \(e\in\{0,1\}\) with
\[
                         mR=nP+eT\quad(m\ \text{odd}).
\]
No saturation at odd primes and no database generator claim is required.

## 3. Two incompatible reductions of the same R

* **At 17:** \(q=\delta u^2\) has squareclass 1. If q has positive or negative valuation, both F,G have unit leading limits there (respectively 9,1 or 1,\(-3/4\)), so \(\beta F,\beta G\) would both have odd valuation. Thus q is a unit and for both x forms to be squares both normalized F,G must have nonzero valuation. The only common zero/pole residues are \(-3/4,1/4\): p17 is outside \(2,3,5,13\) so the branch roots remain distinct except for the two actual shared roots. Of these only \(1/4\) is a square modulo 17. Therefore \(q\equiv1/4\pmod {17}\), and \(x(R)\equiv1\), giving \(R\equiv\pm2P\) since \(2P=(1,-8)\). In \(E_*(\mathbf F_{17})\), P has order 8, with \(4P=(16,0)\ne T\), so T lies outside the cyclic subgroup of P. It follows that \(e=0\) and n is even.
* **At 131:** q has odd valuation. If its valuation is negative, \(G\equiv-3/4\) modulo 131, so \(\beta G\) cannot be a square, because \(\beta\) is square and \(-3\) is not. Thus q has positive valuation. Then \(x(R)\equiv5\) and \(R\equiv\pm P\). Here \(7P=T\), \(2P\ne O\), so P has order 14. The same identity with \(e=0\) gives \(n\equiv\pm m\bmod14\). Hence n is odd.

The contradiction is on the actual multisection, using the same rational ratio point R at both places. There is no contradiction to its being everywhere locally soluble: its separate local points need not have a common Mordell–Weil parameter. The raw Kummer and the new genus-one \((\beta,5,5\beta)\) route remain open.

Replay: `python3 -B replay_mestre_mw_sieve.py | cmp - EXACT-MW-SIEVE-CONTROLS.json`. This uses only tiny exact residue enumerations, old literal source pins, and rational identities. No large number expansion, search over twists, Lean build or remote write.
