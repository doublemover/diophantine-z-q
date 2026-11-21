# The actual consumer accepts a zero ordinate, but the boundary still has a marked rank problem

This concerns the **same** original materialized scalar \(a=0,h=473592745039516333133760\), with \(B=17b=\beta\rho^2\), \(\rho=17c\), \(\mu=\beta c^2=b/17\), \(\delta=1-\mu\) nonsquare, \(\theta=[\delta]\), and \(\beta=204618888056724185\). Keep the exact original two twist equations. This is not a rational point, and does not dispose of the other three exact poles or the anchor.

## 1. Exact original consumer, not just the point-pair type

The published source interface `NormalizedPolePoints318.PointPair.certificate` defines \((e,s_0,p,q)=(T/b,s/b,y_1/(17b),17y_2/((17b)^3s))\). Its only divisions requiring witness nonvanishing are by b and s. The original `PreparedIntegerSource318.complete_at_index` sends the first three resulting certificates through `ThreePoleCertificates318.fill\) and `first263\): the fill assigns the two ordinates to their exact old slots and combines their squared equations in the original detector rows. The original `ThreePoleCertificates318.first263\) explicitly takes unrestricted `Certificate\) and says witness values may vanish. The scalar pair goes via `ScalarCompleteSource318.hasSolution_of_point\), whose proof uses the same `P.certificate hb\) directly in `finish\) and `full_rows\). `finish\) writes C.p, C.q to slots 53,54 and uses the two squared certificate rows, without division by p or q. The terminal rational polynomial projections depend on that same completed assignment. The source byte pins in the manifest identify both direct interfaces and these downstream consumers. No zero-ordinate prohibition occurs in this path. The separate anchor and the previously fixed source row conditions remain exact hypotheses.

## 2. The two boundary quartics and literal inverse

Let \(f(r)=(r^2-\beta)(r^2+3\beta)\), and \(z'=(r^2-\beta)/(r^2+3\beta)\), \(w'=-4\beta r/(r^2+3\beta)\). In the [raw Kummer inverse](../ct-original-scalar-kummer-fiber-r1/ACTUAL-RAW-POINTPAIR-KUMMER-AND-SCALAR-FIBER.md), one may fix the first projective conic parameter to either infinity or zero. The resulting sufficient charts are:
\[
\begin{array}{c|c|c|c}
\text{first slope}&\text{quartic}& T & s/B\\ \hline
\infty&V^2=\delta f(r)&B& V/(r^2-\beta)\\
0&V^2=-3\delta f(r)&-B/3&V/(3(r^2-\beta)).
\end{array}
\]
In both rows put \(y_1=0,\ y_2=\beta\rho^3 s^3 w'\). The identities are exactly \((s/B)^2=\delta(T/B)/z'\) with the first normalized ordinate equal to zero and the second on the same conic. This proves both literal equations with the unchanged second multiplier \(B^2\delta\). No rational root of f exists; there is no rational infinity or r=0 on these quartics for nonsquare positive \(\delta\). Hence a rational point always yields nonzero s and nonzero \(y_2\). Conversely \(y_1=0\) in the actual first equation requires exactly \(T=B\) or \(-B/3\), yielding the displayed boundary charts on the raw Kummer. Symmetry of the raw equation gives the parallel situation for \(y_2=0\).

Both curves are everywhere local. Where \(\delta\) is square, the first has a point at infinity and the second at r=0, including all \(2,3,\beta\) places. At odd primes of even \(\delta\)-depth outside these places, scale off the square power and use smooth genus-one reduction and Hasse. An odd-depth prime outside the fixed support has \(\mu\equiv1\), so \(\beta\) is a local square and \(r^2=\beta\) gives a simple smooth branch point of both quartics. These points can be perturbed to the useful open. At the real place take large r for the first and small nonzero r for the second.

## 3. Elliptic identification, exact signs and the size of the residual mark

For either \(L=\delta,-3\delta\), the literal map
\[
          x=Lr^2,\qquad y=Lr V
\]
gives the x-squareclass \([L]\) on \(E_{\beta L}:y^2=x(x-\beta L)(x+3\beta L)\), with converse by choosing the indicated square root. The quartic is thus the specific dual-isogeny covering for \(\hat\phi:E'_{\beta L}\to E_{\beta L}\) where \(E'_n:y^2=x(x^2-4nx+16n^2)\). The obstruction lies in \(\Sha(E'_{\beta L})[\hat\phi]\), not in the other Sha. Its mark is not a rational torsion class: on the primal curve the nonidentity root classes are \(-3,\beta L,-3\beta L\), and neither prescribed L equals one of them. No rational root can be halved in the positive twist unless \(d=\beta\theta\) is square, and in the negative twist the largest root would require both \(d\) and \(3d\) squares. The other two roots in each case have a negative difference. Odd torsion has trivial image in this quotient.

The base is [24.a4 (24a1)](https://www.lmfdb.org/EllipticCurve/Q/24/a/4) by \(X=x+1\), with bad-place signs \((-1,+1)\) at \((2,3)\), exponent 3 at 2, and nonsplit multiplicative at 3. Here \(d\equiv17\bmod24\). The positive twist has split multiplicative reduction at 3, the same 2-place, and root number **minus**. For the negative twist \(-3d\), the 2-character is the nontrivial **unramified** one (class −3), reversing the 2-sign because the conductor exponent was odd. The ramified quadratic twist of the multiplicative factor at 3 has sign \((-1/3)=-1\). In both twists the odd primes of d contribute the product \(\prod_{p\mid d}(-1/p)=+1\), since d is 1 mod4 and coprime to 6; the real sign is −. Thus the negative twist has root number **plus**. These are local epsilon-factor signs (unramified twist multiplies by the character of uniformizer to the conductor power; ramified quadratic twist of a multiplicative or good factor contributes the square of its normalized quadratic Gauss sum). Neither sign is an algebraic rank certificate.

For the minus-sign choice \(n=d=\beta\theta>0\), the primal x-squareclass Selmer panel is exact on signed divisors of \(3d\). At odd p|d, \(E_d(\mathbf Q_p)/2\) is the four rational torsion triples by independent valuation pairs, so the x projection is \(\langle-3,d\rangle\). Thus only split \((-3/p)=+1\) primes impose one equation each. At 3 the two generators span all four squareclasses. At 2 x has even valuation; the local points \((3,6)\) and \(T_0\) on the untwisted model already give first unit classes 3 and 5, hence all units; at infinity both signs occur. Good odd places impose no extra row on this signed support. Therefore \(\dim\mathrm{Sel}^{\hat\phi}(E'_d)\ge2+\#\{p\mid d:(-3/p)=-1\}\ge9\), using \(5,11,17\) and the four visible θ primes. Rank one would still leave dimension at least six in \(\Sha(E'_d)[\hat\phi]\) because its rational x-image has dimension at most three. So the simple rank certificate must also control the mark.

An exact positive fact: the ordered **full** class \((\theta,1,\theta)\) lies in \(\mathrm{Sel}_2(E_d)\) unconditionally on the literal scalar. It is trivial locally at all primes of \(\beta\) and at 2,3,∞. At every θ prime \(\beta\) is a square, so the triple is exactly the local rational-root class of \(T_d\). All other odd places are unramified good. The class differs by that rational-root triple from \(\eta=(\beta,1,\beta)\). A rational point of the latter mark gives the former by adding the same rational torsion point, thus gives the original boundary. The next section reports the exact present primal dimension cut, independently of the larger dual group. Without controlling the first projection, a boundary point could realize the first class with a different second entry; a nonzero pairing of the chosen full lift alone would not exclude competing lifts.

## 4. Exact primal Sel₂ rows and visible arithmetic

In root order \((0,d,-3d)\), write a positive pair \((r,s)\) for the first two slots; positivity is imposed by multiplying by rational \(T_0\) if the two real signs are negative. Write \(a_p=v_p(r), b_p=v_p(s)\) mod2 for all p|d, and allow also \(a_3,b_2\). There are no other primes in the two slots: at 3 \(s\) is square, and at 2 \(r\) has even valuation. Using the same Legendre matrix \(\mathcal L\) as the previous exact new-Mestre calculation (actual diagonals \(D_p=[d/p]\)), the rows at odd p|d are
\[
 (\mathcal L a)_p+[3/p]a_3=[-3/p]b_p,\qquad
 (\mathcal L b)_p+[2/p]b_2=[-1/p]b_p.
\]
They follow by stripping the local torsion patterns \(T_d^{a_p}T_0^{b_p}\). At 3 the single row is \(s\equiv1\bmod3\). At 2 the full group is spanned by unit-pair labels \((5,7),(3,2),(1,5)\) from \(T_0,x=3,x=1/4\); for the last, \(y^2=-39/64\) is a 2-adic square. These generate eight classes, the order of \(E_d(\mathbf Q_2)/2\). Thus the two remaining rows are
\[
 b_2=[r\equiv3\ (4)],\qquad [s/2^{b_2}\equiv3\ (4)]=[-2/r].
\]
The last notation is the Kronecker nonsquare bit, equivalently r≡5 or7 mod8 for positive odd r.

The exact replay on the eight \(\beta\) and four visible θ primes, with the two indicated 3 and 2 variables, gives rank **23/26** before unseen local rows. It has positive kernel of dimension three, one generator \((\beta,1)\) and two test pairs \(e_1,e_2\) recorded in the replay. **If there is exactly one unseen θ prime** P, then P≡13 mod24, all its forward Legendre bits are the literal aggregate, and reciprocity gives the reverse row. Adding both columns and its two rows gives rank **24/28**, positive dimension four, hence full primal \(\dim\mathrm{Sel}_2(E_d)=5\). Under that hypothesis the extra positive line modulo the visible kernel is generated by \((\theta,1)\), which differs from \((\beta,1)\) by torsion. All three visible generators really are then admitted. Moreover the four positive first-coordinate masks are linearly independent (the replay checks rank four), so the positive first projection is injective under this hypothesis. In particular the boundary first class [θ] then has the **unique** full lift (θ,1,θ). This is a contrast with **dimension three** for the conditional same-scalar new Mestre curve; the boundary removes the norm gate but does not let rank alone certify its mark.

## 5. Literal Cassels row for the boundary mark

For a genuine test \((r,s,rs)\in\mathrm{Sel}_2(E_d)\), the [ordinary Cassels tangent formula](https://doi.org/10.1515/crll.1998.001) gives, in multiplicative sign convention, the following **exact** row:
\[
 \boxed{\quad (-1)^{v_2(s)}\left(\frac{s}{D}\right)
            \prod_{p\mid\theta}\left(\frac2p\right)^{v_p(r)}
                                 \left(\frac6p\right)^{v_p(s)} \quad}       \tag{*}
\]
Here \(D>0\) is the reduced denominator of the literal c; v2(s) is the binary 2-depth of its representative. In particular it is not a function of the known θ factors alone.

Use the equivalent model \(n=\beta\delta\) and marked triple \((\beta,1,\beta)\). In variables \((t,u_0,u_1,u_2)\) the three conics omit \(u_0,u_1,u_2\) respectively, with equations
\[
 \beta u_2^2-u_1^2=4\beta\delta t^2,\quad
 u_2^2-u_0^2=3\delta t^2,\quad
 \beta u_0^2-u_1^2=\beta\delta t^2.
\]
Rational tangent forms are \(L_0=u_2-cu_1-2\delta t,\ L_1=u_2-u_0,\ L_2=u_0-cu_1-\delta t\): for the first and third use the rational points \((u_2,u_1,t)=(2,2\beta c,1)\), \((u_0,u_1,t)=(1,\beta c,1)\); for the middle use \((u_2,u_0,t)=(1,1,0)\). The Cassels product is \((L_0L_2,r)_v(L_1L_2,s)_v\). Multiplying each by \((2,rs)_v\) leaves the global product unchanged.

* At a fixed \(\beta\) prime or at 3 choose \(w=\sqrt\delta\equiv1\pmod p\), and the point \((t,u_1,u_0,u_2)=(1,0,-w,-2w)\). Here \([L_0L_2]=[2]\), \([L_1L_2]=[1+w]=[2]\); the corrected factor is trivial. At the real place the same point gives positive factors.
* At 2 use the same point with \(w\equiv1\bmod8\). The **literal scalar** has \(v_2(\mu)=4\), so \(w\equiv9\bmod16\), \([1+w]=[10]\). Thus the corrected factor is \((5,s)_2=(-1)^{v_2(s)}\).
* At p|θ take \(t=0,u_0=1,u_2=-1,u_1=-\sqrt\beta\) with \(h_*=c\sqrt\beta\equiv1\). Then \(L_0L_2=-\delta\) exactly and \(L_1L_2=-2(1+h_*)\sim -1\), so the corrected factor is \((-2\delta,r)_p(-2,s)_p\). Locally \((r,s)=(\delta^a(-3)^b,(-\delta)^b)\) in squareclasses, giving exactly \((2/p)^a(6/p)^b\). This choice also handles positive **even** depth of \(\delta\), where both tests are units and the factor is trivial.
* At an odd good prime with c integral and δ a unit, each tangent is primitive on its smooth conic and its valuation at a primitive projective point off its zero is even. A simple verification: if reduction lands on the tangent point, choose a unit local projective coordinate at that point, so the tangent coordinate equals a unit times the square of the local conic parameter; otherwise evaluation is a unit. For each projected conic, primitivity follows from the three equations and all model coefficients being units. Thus all corrected factors are trivial. If \(v_p(c)=-e<0\), put \(t=p^e T,\ \tilde c=p^e c,\ \tilde\delta=p^{2e}\delta\); both latter entries are units. In these smooth conic models \(p^eL_0,p^eL_2,L_1\) are primitive tangents and have even valuations. The transformed rational tangent points are given by \(T=1,u_i=p^e\) or \(2p^e\), \(u_1=\beta\tilde c\) or \(2\beta\tilde c\), respectively, so no extra common factor is lost. Therefore \(v(L_0L_2)\) is even, \(v(L_1L_2)\equiv e\pmod2\), and the sole contribution is \((s/p)^e\). This is the displayed Jacobi symbol, not a known sign.

Under the one-unseen hypothesis, the two genuine visible pure tests have second classes
\[
 S_1=2952271997968816765,\qquad S_2=5566083893370034
\]
and signs against the mark respectively \(-\,(S_1/D)\) and \(+\,(S_2/D)\). At the four fixed literal denominator primes \(29,181,1346909,70850399941\), known to have depth one, their products are respectively + and −. The two actual checks on the remaining odd-depth denominator product \(D_{\rm exc}\) are therefore **both** \((S_i/D_{\rm exc})=-1\) for the mark to lie in the ordinary Cassels radical. If either fails, the specified boundary has no rational point under this input hypothesis. No value of either residual symbol is supplied. Even if both pass, a point is not proved: for example one could combine a nontorsion certificate with a nonzero pairing between the other two pure directions to make the radical exactly the marked line. This global mark problem is separate from the accepted zero-ordinate downstream interface.

The exact replay checks the bit matrices, both actual candidate signs and the fixed denominator parts. The local tangent calculation above is the proof of (*), not an inference from the replay. No local Lean build, expanded literal coefficients, or remote write.
