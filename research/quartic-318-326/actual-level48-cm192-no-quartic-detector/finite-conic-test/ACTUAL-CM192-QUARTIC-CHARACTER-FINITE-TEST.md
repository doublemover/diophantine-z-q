# A conic-and-residue test for a quartic detector of the marked class

For either actual balanced twist there is an exact class-group square root of the marked ambiguous class from a norm conic. An order-four unramified character detecting the marked class exists if and only if a finite system of quadratic characters passes explicit tests on this square root and on a finite generating set for the full \(2\)-torsion class group. The test needs no CM class-orbit enumeration and no factorization of the conic trace denominators. No passing character for an actual selected twist is supplied here. Even a passing character would **not** evaluate the still unknown signed Heegner intersection ideal.

## 1. The marked square root from one small norm conic

Use \(F=\mathbf Q(\sqrt3,\sqrt{17})\), \(E=\mathbf Q(\sqrt{17})\), \(D=-n\) and \(L=F(\sqrt D)\) for one of the actual balanced detected twists, with the \(n\equiv23\bmod24\) refinement. Write \(\beta=17B_*\), as in the quadratic genus obstruction. Thus \(17\) and all primes dividing \(B_*\) divide \(n\); the genuine primes in \(B_*\) are \(1\bmod408\); the fresh \(q_0\) lies outside \(\beta\). The marked ideal
\[
 \mathfrak B=\prod_{p\mid B_*}\prod_{\mathfrak P\mid p}\mathfrak P
\]
has exact class order two in \(\mathrm{Cl}(L)\). The fixed field \(F\) has class number one by the reviewed Minkowski calculation.

In fact \(B_*\) is a global norm already from \(E(\sqrt D)/E\), so there is an exact conic solution
\[
 a,b\in E,\qquad a^2-Db^2=B_* .\tag{1}
\]
Here are all the local rows, explicitly for the same \(n\) and \(\beta\).
- At a genuine \(p\mid B_*\), \(p\) splits in \(E\) and the level curve is at an odd ramified twist prime. The actual local Kummer mark \((\beta,1)\) has valuation pair \((1,0)\), hence is the rational torsion image \((n,1)\), by the bijective local torsion valuation table. Thus \(n/\beta\) is a square unit and \(B_*/(-D)=1/(17(n/\beta))\) is a square unit in \(E_\wp\); \(B_*\) is the norm of \(\sqrt D\) times a unit square.
- At \(p\mid n,\ p\nmid\beta\), the local mark has zero valuation pair, hence is trivial by that same odd-place table. Thus \(\beta\) is a local square, and \(B_*\) is a square in \(E_\wp\) because \(17\) is a square there.
- At 17, adjoining \(\sqrt D\) to \(E_\wp\) is the same as adjoining the square root of the rational unit \(D/17\). This is split or unramified, so the unit \(B_*\) is a norm. At 2 and 3, \(D\) is already a rational local square; the extension splits.
- At every other finite place the extension is split or unramified, and \(B_*\) is a unit. At each real place \(B_*>0\) is a complex norm.

The quadratic Hasse norm theorem, equivalently Hasse–Minkowski for the norm conic, gives (1). It is existence for the exact arithmetic target, not an evaluated conic on a numeric selected pair. Put \(\alpha=a+b\sqrt D\), and view it in \(L\). At each relative ramified prime over \(B_*\), its valuation is one; at all other relative ramified primes it is zero. At an inert prime of \(L/F\) it is a unit. At a split pair over a place \(\wp\), its two opposite valuations sum to zero, since \(B_*\) is a unit there. Choose the positive side as an ideal \(\mathfrak c_B\), yielding
\[
 (\alpha)=\mathfrak B\,\mathfrak c_B/\overline{\mathfrak c_B}.
\]
Conjugation acts by inversion on \(\mathrm{Cl}(L)\) since \(\mathrm{Cl}(F)=1\), so \([\mathfrak c_B]^2=[\mathfrak B]\). This is a proof-producing square root from a single norm solution, independent of any Heegner point calculation.

## 2. Two possible positive-unit ambiguity directions

For a totally positive unit \(u\in O_F^\times\) which is a norm from \(L\), use an exact \(a_u+b_u\sqrt D\) of norm \(u\) similarly. There are no positive valuations at relative ramified primes in this case, and all nonzero ideal exponents are opposite on relative split pairs. This gives
\[
 (a_u+b_u\sqrt D)=\mathfrak c_u/\overline{\mathfrak c_u},\qquad
 [\mathfrak c_u]^2=1.
\]
The complete *positive* \(F\)-unit squareclasses are spanned by
\[
 \epsilon_3=2+\sqrt3,\qquad
 \epsilon'=(4+\sqrt{17})(1+\sqrt3)(7+\sqrt{51})/2.
\]
Indeed the two factors \(\epsilon_{17}=4+\sqrt{17}\) and \(\epsilon_*=(1+\sqrt3)(7+\sqrt{51})/2\) have the same real signature, depending only on the sign of \(\sqrt{17}\), and \(-1\) is negative at every embedding. This uses the exact unit basis from the quadratic genus paper. To determine the local norm subspace among the four positive classes, test that the unit is a square in the residue field at **every** relative ramified prime of \(F\), namely above \(p\mid n,\ p\ne17\). For these odd ramified quadratic extensions this is precisely the unit norm condition. All other finite places are split or unramified and impose nothing on a unit; the real places impose only positivity. Thus local tests and one certified conic solution for each basis class suffice. In particular at most two such conics are needed.

On the first arm \((u,v)=(1,\theta)\) without a repair prime, \(\epsilon_3\) is a norm with a particularly direct construction. Every prime of \(n\) splits in \(\mathbf Q(\sqrt2)\): the genuine and helper primes are \(1\bmod24\), 17 is \(1\bmod8\), and \(q_0\equiv7\bmod24\). The real quadratic field has class number one by its Minkowski bound \(\sqrt8/2<2\). Multiply one principal factor for each prime of \(n\) and adjust by the norm-\(-1\) unit \(1+\sqrt2\), obtaining integral \(x+y\sqrt2\) with \(x^2-2y^2=-n\). Since \(y\ne0\), the element
\[
 \frac{1+\sqrt3}{2}\cdot\frac{x+\sqrt D}{y}
\]
has norm \(\epsilon_3\) from \(L\) to \(F\). This uses only exact quadratic norm arithmetic in the listed prime factors; no class count in \(L\).

The ramified prime ideal classes of \(L/F\), together with these \([\mathfrak c_u]\) for a basis of positive norm units, generate **all** \(\mathrm{Cl}(L)[2]\). To prove this, choose a fractional ideal \(J\) representing an element of order dividing two. Then \(J/\bar J=(\gamma)\) is principal. Its generator has norm a totally positive \(F\)-unit (the norm of the principal ideal is trivial). Choose its representative unit class \(u\), and rescale \(\gamma\) by a unit in \(F\) to make its norm exactly \(u\); one may multiply the supplied conic elements according to the unit basis. Divide by the chosen norm-\(u\) element; the result has norm one, so is \(\delta/\bar\delta\) by Hilbert 90. Thus \(J/(\mathfrak c_u(\delta))\) is an invariant ideal. Such ideals consist of extensions of \(F\)-ideals and powers of ramified primes, with the former principal. This gives the assertion in the class group. Conversely the displayed generators all have order dividing two. For clarity \(O_L^\times=O_F^\times\): a unit divided by its conjugate has norm one and is \(\pm1\); the minus sign would give a unit in \(\sqrt D F\), impossible at any relative ramified prime, where that valuations' parity is odd. The generating argument does not assume that every ambiguous ideal class has an invariant ideal representative.

## 3. Factorization-free evaluation of the conic-ideal characters

Use the complete finite panel \(\chi_t\) of quadratic unramified characters of \(L\) from the genus paper: \(t\in F^\times/F^{\times2}\) supported in the finite relative ramified set, units allowed, and the exact dyadic unramified tests. At a finite relative ramified prime \(\mathfrak P\mid\wp\), the character is the residue symbol of \(t D^{-v_\wp(t)}\). At all finite places of \(F\) outside the relative ramified set, \(F(\sqrt t)/F\) must be split or unramified, since \(L/F\) itself is split or unramified there. This includes the two dyadic places.

For either type of norm conic above, let \(s=2a\in F\) be the trace of its solution. If \(s=0\), its split-pair opposite valuations must both be zero (otherwise their sum as elements has a term of strictly smaller valuation and is nonzero); in that case declare its denominator ideal to be the unit ideal. In general form the denominator ideal
\[
 \mathfrak d(s)=\{z\in O_F: zs\in O_F\}.
\]
It is exactly \(N_{L/F}(\mathfrak c)\) for the positive-side ideal in §1 or §2. At relative split pairs the trace has valuation \(-|v(\alpha)|\) when the two opposite valuations are nonzero, since unequal valuations cannot cancel; if both vanish the trace is integral. At inert or ramified places the norm target has nonnegative valuation and the solution is integral, so no denominator occurs. This computation uses the trace \(2a\), not \(a\), so it also holds at 2. In particular the denominator is prime to every relative ramified \(\wp\).

The character value on \(\mathfrak c\) equals the quadratic Artin symbol of \(t\) on \(\mathfrak d(s)\) over \(F\). The denominator ideal can be formed by integral lattice arithmetic in \(F\), and has a generator \(g\) because \(\mathrm{Cl}(F)=1\). One need not factor the denominator. At every finite place outside the relative ramified set the unramified formula \((t,g)_\wp=(t/\wp)^{v_\wp(g)}\) holds, while the product over all places is one. Hence
\[
 \boxed{\chi_t(\mathfrak c)=
       \prod_{\wp\ \mathrm{relative\ ramified}}(t,g)_\wp
       \prod_{v\mid\infty}(t,g)_v .}\tag{2}
\]
At these odd relative ramified places \(g\) is a unit, so the \(v_\wp(t)\) odd rows are just its residue signs; the other rows are one. Signs at the four real embeddings supply the final factors. The formula is independent of the principal generator chosen. This is an exact arithmetic replacement for factorization or class enumeration, not a claim about the bit complexity of finding the conic solutions or the fixed-quartic generators.

## 4. Exact separating-character test and one remaining blindness

Let \(G=\mathrm{Cl}(L)\). An order-four character with value \(-1\) on \([\mathfrak B]\) exists **if and only if** some quadratic \(\chi_t\) satisfies all of the following finite tests:
1. It is trivial on every relative ramified prime class.
2. It is trivial on all the positive-norm-unit classes \([\mathfrak c_u]\) from §2, via (2).
3. It has \(\chi_t(\mathfrak c_B)=-1\), via (2).

Indeed a quadratic character of a finite abelian group has an order-four (or order-dividing-four) square root precisely when it is trivial on \(G[2]\). This follows by checking cyclic primary factors, or defining the character on \(2G\) by its values on preimages and extending. Any square root then has value \(\chi_t(\mathfrak c_B)\) on \([\mathfrak B]=[\mathfrak c_B]^2\), independent of which square root was chosen. Conversely a separating order-four character has a square satisfying these tests. The tests can be imposed jointly as linear equations on the quadratic squareclass panel once the norm conics are supplied. They characterize whether the marked class survives in \(G/4G\). No assertion that it survives in the literal profiles follows without evaluating the tests.

In making this test it does not suffice to use only \(t\) from \(E=\mathbf Q(\sqrt{17})\). For the solution of (1) in \(E\), the trace denominator in \(F\) is extended from its denominator over \(E\). If \(t\in E^\times\), the Artin symbol of \(t\) on that extended ideal is one. At primes where \(F/E\) is unramified this follows by summing the two split evaluations or squaring by residue degree two; if \(E(\sqrt t)\) were ramified there it would remain ramified in \(F\), contradicting the unramified requirement at the relative split denominator primes. At primes ramified in \(F/E\), the extended ideal has even exponent and again evaluates to one. Therefore \(\chi_t(\mathfrak c_B)=+1\) on this entire subfield panel, including every rational candidate such as \(t=B_*\), whether or not it kills the ambiguity directions. A successful test requires a genuinely quartic-base squareclass \(t\) and supplied global conic data. It would still leave evaluation of its quartic lift on the unknown **signed Heegner intersection ideal** as a separate problem.

### Exact dependence

The class field, unit basis and quadratic panel are from *Ordinary genus characters cannot see the marked relative ideal class*, paper **9ebfd5382aca7956109e91584026cf5a43444aaf2902d46e64c42c845c1341ef**. The actual same CM sign receiver is *The next marked sign from a relative ideal-class relation*, paper **7500994322c7257e29c58aa2411f77e23276a49871c4cd7ae1c893db73c45e4d**. This is a finite proof interface, not a numerical certificate that it has a solution on a selected curve.
