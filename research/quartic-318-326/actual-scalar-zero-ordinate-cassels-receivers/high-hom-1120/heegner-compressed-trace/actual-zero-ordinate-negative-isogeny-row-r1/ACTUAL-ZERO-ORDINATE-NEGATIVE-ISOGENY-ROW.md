# An exact first Cassels test for the negative zero-ordinate boundary

Keep the [literal zero-ordinate receiver](../../../rc-native-helper-20261120/ct-original-scalar-zero-ordinate-boundary-r1/), with the actual \(\beta=204618888056724185,\ \mu=\beta c^2,\ \delta=1-\mu>0\), and positive squarefree \(\theta=[\delta]\). Thus \(d=\beta\theta\), \(\gcd(\beta,\theta)=1\), and \(\delta\) is a square at \(2,3,\infty\) and at every prime of \(\beta\). Under the actual scalar, all four currently known odd \(\theta\) primes split in \(\mathbf Q(\sqrt3)\). No assumption is made here about the number of unseen primes.

The two branches are
\[
 \mathcal C_+:\ V^2=\delta(t^2-\beta)(t^2+3\beta),\qquad
 \mathcal C_-:\ V^2=-3\delta(t^2-\beta)(t^2+3\beta).
\]
Write \(M=\delta\) or \(M=-3\delta\), \(n=\beta M\), and
\(E_n:y^2=x(x-n)(x+3n)\), \(E'_n:y^2=x(x^2-4nx+16n^2)\). The literal map \(x=Mt^2,\ y=MtV\) is the dual-isogeny cover with class \([M]\) in \(S^-(n)=\operatorname{Sel}^{(\hat\phi)}(E'_n)\), using the isogeny from \(E_n\) whose kernel is \((0,0)\). In particular the covering torsor is under \(E'_n\), not under \(E_n\).

## 1. Exact negative isogeny panel

The negative group is the subgroup of the positive first-slot panel cut out by \(e\equiv1\bmod4\): explicitly the signed squarefree \(e\mid3d\) satisfying
\[
 e\equiv1\bmod4,\qquad
 \left(\frac{e/p^{a_p}}p\right)
 =\left(\frac{d/p}p\right)^{a_p}
 \quad\text{for every }p\mid d\text{ with }(-3/p)=1,\qquad a_p=v_p(e).
\]
At a good odd prime not dividing \(3d\), the isogeny image consists of all unit classes, by the degree-two local quotient on the good reduction and isomorphism on the odd formal subgroup. At odd \(p\mid d\) the full local two-quotient has size four, supplied by the four torsion points (a nonzero root cannot be halved since the two other root differences have odd depth). Their first slots give \(\langle-3,n\rangle=\langle-3,d\rangle\). Thus precisely the split primes impose the displayed odd rows. At 3 the first slots \(-3,-3d\) are independent because \(d\) is a nonsquare unit. The real first slots include both signs.

At 2 the curve \(E_n\) is isomorphic to \(E_{-3}\), since \(d\) is a square unit. For \(x\) of nonzero depth, that depth must be even by the equation \(y^2=x(x+3)(x-9)\). If \(v_2(x)>0\), the two other factors' product is 5 modulo 8, hence the stripped \(x\) has class 5; if \(v_2(x)<0\), their product after dividing by \(x^2\) is 1 modulo 8, hence \(x\) has class 1. For \(x\equiv3\bmod4\), put \(x=3+4k\): the square condition would require \(x(4k^2-9)\equiv1\bmod8\), but it is 5 for both parities of \(k\). Thus only \(x\equiv1\bmod4\) remains and gives unit classes 1 or 5. Both are supplied by identity and the root \(0\) class \(-3\). This is precisely the stated extra mod-4 condition. The positive group has all four unit classes at 2 as in the original boundary.

## 2. Exact pairing on the negative row, without the denominator

Use the [Fisher pushout function already derived for this quartic geometry](../actual-scalar-kummer-isogeny-and-marked-pairing-r1/). The rational branch point on the pushout conic is \((t^2,V)=(\beta,0)\); this produces function \(\beta(z^2+3M)\), \(z=V/(t^2-\beta)\), of squareclass \(\beta M(t^2-\beta)\). Rational multiplicative constants do not change its global Hilbert product. For \(e\in S^-(-3d)\) use \(g=(t^2-\beta)/(-3\delta)\) and obtain
\[
 (-1)^{2\langle[-3\delta],e\rangle}
   =\prod_v(g(P_v),e)_v
   =\boxed{\prod_{p\mid\theta}\left(\frac3p\right)^{v_p(e)}} .
\]
Indeed, at every \(\theta\)-prime the exact source identity \(\delta=1-\beta c^2\) makes \(\beta\) a local square, and one can take a point sufficiently close to the branch \(t^2=\beta\). Then \(t^2+3\beta\) has square class \(4\beta=1\), so \(g\) is a square by the quartic equation. At \(2,3,\infty\) and every \(\beta\)-prime, \(t=0\) gives \(V^2=9\beta^2\delta\), and \(g\) has squareclass \(3\beta\). At any remaining odd prime, \(e\) is a unit and \(g\) has even valuation: a pole of \(t\) gives even depth, and a positive depth of \(t^2-\beta\) leaves the other factor a unit so parity follows from the equation and even depth of \(\delta\). Global reciprocity with the fixed \(3\beta\) now gives the formula, since \((3\beta,e)_p=(3/p)^{v_p(e)}\) at the \(\theta\)-primes. The resulting product is precisely the pairing of the zero-ordinate negative cover, not of the separate slope-\(1/c\) cover with \(\lambda=1+3\mu\).

On \(\mathcal C_+\) take \(g=(t^2-\beta)/\delta\); it is a square near the same branch at every \(\theta\)-prime and near infinity at the old places. All other Hilbert factors vanish by the same parity argument. So the **positive first isogeny row is always zero**, independently of actual hidden support, in accord with the full two-descent lift already proved there. Its later ordinary Cassels denominator character is not addressed by this first-row calculation.

A compact negative certificate for the original negative branch can therefore use any explicitly supplied signed squarefree \(e\equiv1\bmod4\) with support in \(3\beta\theta\) and exact
\[
 X^2-eY^2=-3\beta\delta/e,\qquad X,Y\in\mathbf Q(\sqrt{-3}),
 \qquad
 \left(\frac3{|e|/\gcd(|e|,6\beta)}\right)=-1 .
\]
The displayed norm equation is equivalent to the odd split-place admission on this domain: the symbol \((e,-3\beta\delta/e)\) over \(\mathbf Q\) vanishes after restriction to \(\mathbf Q(\sqrt{-3})\) automatically at nonsplit places (local degree two) and at all good unit places. At split \(p\mid d\) its vanishing is exactly the odd row in §1, by the valuation-one local Hilbert formula applied after removing square factors of \(\delta\); this also explains why the raw rational \(\delta\) can be used in the norm. This does not assume an available factorization of \(\theta\) or knowledge of any exceptional denominator prime. It does require genuine admission and nonzero sign, neither of which follows from just a nominated \(e\). All four known actual \(\theta\) primes have sign \(+1\), so no test confined to the known support can obstruct \(\mathcal C_-\) by this first pairing.

## 3. A support-independent correction lemma and a nonproduction control

The five old split rows at \(163,661,733,1489,1861\), together with the mod-4 row, have rank six on the ten old columns \(-1,3\) and the eight \(\beta\) primes. Their diagonals are already exact, because \(\delta\) is a square at each old prime. Consequently **if there is no new split-\((-3)\) \(\theta\)-prime**, then for any chosen \(\theta\)-prime \(q\) with \((3/q)=-1\), one can multiply \(q\) by a product of old columns to obtain a genuine negative-group test. Its pairing is \(-1\), and the actual negative branch would have no rational point. The rank statement is valid independently of how many additional split rows there are; when such rows exist, they must also be checked and this automatic correction no longer asserts admission.

Here is an exact same-\(\beta\), standalone Ready control, **not** the materialized scalar: take \(c=12/5428178401\), \(b=17\beta c^2\). Then \(D^2-144\beta=872914634161=53\cdot16470087437\), a product of two primes each \(5\bmod12\) and coprime to \(D\beta\). The denominator is prime to \(6\beta\); \(b>0\), \(b<17\), and its 2-, 3-, and 17-valuation guards follow from its displayed numerator. Both negative and positive quartics are locally soluble as in the boundary construction. The exact test \(e=-18444371=-11\cdot17\cdot1861\cdot53\) passes all six rows, and \((3/53)=-1\). Hence this negative boundary has no rational point; that is a check of the formula, not a rejection of any original actual pole or of its positive/other charts.

No actual \(\theta\)-prime with \((3/q)=-1\), norm certificate, Cassels obstruction, or rational point is supplied for the unchanged scalar. The test is unconditional as a receiver, not as an evaluated sign. It uses the first-isogeny lift criterion only: vanishing of the row does not imply a rational point or rank.

    python3 -B check_zero_ordinate_negative_row.py | cmp - EXACT-NEGATIVE-ROW-CONTROL.json
