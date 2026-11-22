# A known first point and an exact one-bit trace criterion on the old literal input-0 scalar

Fix the OLD compact surviving scalar
\(a=0,\ h=473592745039516333133760,\ i=6^{15}3^{65536}J\)
with its pinned \(J,c\), and write
\[
 \beta=204618888056724185,\quad
 \rho=17c,\quad B=17b=\beta\rho^2,\quad
 \delta=1-\beta c^2>0,\quad K=\mathbb Q(\sqrt\delta).
\]
Take the **free first twist choice \(t=18\)**, independently of the
earlier fixed chart \(z=1/100\). An exactly certified known first
rational point on a finite integer cubic scales to this literal
old \(b\); no useful rational isogeny can directly transport it
to the nonsquare companion. The exact remaining **full ordered**
companion mark is rational if and only if a certain quadratic
Mordell–Weil index equals two. This index is not evaluated.

## 1. The known point really scales to the old literal \(B\)

Put \(A=1+3\beta t^2\), \(n=\beta(1-\beta t^2)(1-9\beta t^2)\), and
\[
 F=E_n:\ Y^2=X(X-n)(X+3n),\qquad
 P=(\beta A^2,\ 8\beta^2 tA(1-3\beta t^2)).
\]
Here \(n=8094120968054829661910126903116889587959583856144085429185\).
The old [exact rank-one packet on this same \(F\)](https://github.com/doublemover/diophantine-z-q/blob/f767adfb8eba61b98fc865e82f73776f4f095799/quartics/quartic-318-326/proof/recovery/20261118/indexed-free-first-twist-rank-one/README.md)
(SHA-256 57875a3c1c2d7a5c8e57fcd46b4f978e95895c9a511f830f59561a590bb2cf65)
certifies \(F(\mathbb Q)/2F(\mathbb Q)\) with basis given by
\(P\) and the two independent rational \(2\)-torsion points
\(T_0=(0,0), T_n=(n,0)\). Specifically its displayed Selmer basis
uses \(P,T_0,P+T_n\), an equivalent basis. The old rank-one result
about this first curve depends only on the **same** \(\beta,t\),
not on which source scalar carries it. Directly
\(X-n=(4\beta t)^2,\ X+3n=\beta(2(1-3\beta t^2))^2\), so its
ordered pair in the \((X,X-n)\) slots is \((\beta,1)\).

On the present archived scalar define \(T=n(\rho/A)^2\) and
\(F'=E_{n\delta}\). Scaling \(P\)'s coordinates by
\((\rho/A)^2,(\rho/A)^3\) gives the first point at **exactly**
\(x=B\) on \(E_T\). If \(Q\in F'(\mathbb Q)\) has ordered pair
\((\beta,1)\), write \(x(Q)=\beta q^2\), \(q\ne0\).
Scale its coordinates by \((B\rho/A)^2,(B\rho/A)^3\);
the second parameter is \(T B^2\delta\), and its scaled
abscissa is \(B s^2\) with \(s=qB/A\ne0\).
This is exactly the old scalar PointPair on the chosen free twist.

On \(F'\), rational \(4\)-torsion is impossible: at 6551 all
differences of distinct roots have odd valuation. The rational
torsion \(x\)-classes therefore come from the identity and the
three roots, namely \(1,-3,n\delta,-3n\delta\). None equals
\(\beta\): the identity is square, \(-3\) is negative, and the
last two have odd valuation at 6551. Any exact lift is hence
nontorsion. Moreover \(E_n\) has nonintegral \(j=35152/9\) and
has no geometric complex multiplication. A nontrivial elementary
quadratic twist of such an elliptic curve has zero rational Hom
from it: the twist character negates the geometric Hom generator.
Since \(\delta\) is nonsquare, no nonzero rational isogeny or
chain of rational isogenies transports \(P\) to \(F'\).
Adding rational torsion cannot evade this absence of a rational
map or create a marked point from torsion.

## 2. Exact two-place restriction on everywhere-local traces

The ordered pair \((\beta,1)\) belongs to the full Selmer group
of \(F'\) for the present \(b\). Here is the local argument without
factoring \(\delta\). At \(2,3\) and primes of \(\beta\) the archived
preparation makes \(\delta\) a square, so the known \(P\)
transports in those local fields. At real infinity \(\delta>0\).
At the remaining odd places where \(v_p(\delta)\) is odd, it is
positive and \(\beta c^2\equiv1\bmod p\); the \(\beta\) slot is
square. Where \(p\mid n,\ p\nmid6\beta\), one of
\(1-\beta t^2,1-9\beta t^2\) vanishes modulo \(p\), again giving
a square \(\beta\). Everywhere else the model has good reduction
after an even-depth square scaling and both slots are units;
at odd good reduction with full rational \(2\)-torsion the complete
unramified unit Kummer pairs occur. This last fact also follows
from the smooth reduction group modulo doubling, of size four,
and the formal group on which doubling is invertible.

The literal \(\delta\) has valuation one at 6551 and 16782959.
The [published 6551 source replay](https://github.com/doublemover/diophantine-z-q/blob/f767adfb8eba61b98fc865e82f73776f4f095799/research/quartic-318-326/actual-scalar-specialization/ACTUAL-THETA-MODULAR-ROWS.md)
gives \(\delta/6551\equiv684\bmod6551\); the
[second named prime replay](https://github.com/doublemover/diophantine-z-q/blob/f767adfb8eba61b98fc865e82f73776f4f095799/research/quartic-318-326/heegner-actual-theta-bounds/source/ACTUAL-TWO-ADDITIONAL-H-PRIMES.md)
gives \(\delta/16782959\equiv13715188\bmod16782959\).
Each place is a ramified quadratic place of \(K\) and a good
place of \(F\). The trace from \(F(K_p)\) reduces to the
doubling map in the common residue field since conjugation
acts trivially on it. At 6551 the difference signs
for \(T_0,T_n,T_{-3n}\) are \((+,-),(-,-),(+,+)\);
at 16782959 they are \((-,+),(+,+),(-,-)\).
By the split-root halving criterion, only \(T_{-3n}\) can be
halved at the first place, and only \(T_n\) at the second.
Thus no nonidentity rational \(2\)-torsion element is
an everywhere-local trace. Neither place alone excludes all three.

This is not the quadratic field of the earlier published
[t=18 trace theorem](https://github.com/doublemover/diophantine-z-q/blob/f767adfb8eba61b98fc865e82f73776f4f095799/quartics/quartic-318-326/proof/recovery/20261118/actual-rank-one-trace-index-and-relative-sha/actual-free-index/ACTUAL-T18-UNMARKED-INDEX.md)
at \(h=328655617654071015360\): its complement has odd depth at 61,
whereas the current old \(h,J\) evaluation gives \(c\equiv55\),
\(\delta\equiv50\) modulo 61, a nonsquare **unit**. In this
comparison the actual \(i\)-point is formal, the actual \(h\)
chart has unit norm, and \(Q_{\rm pack}\equiv0\). The replay
certifies the untouched elliptic calculation at this one prime.
In particular the previous partner support output is not imported.

## 3. Both directions of the one-bit criterion

Let \(j:F'_K\to F_K\) be the twist isomorphism
\((X,Y)\mapsto(X/\delta,Y/(\delta\sqrt\delta))\).
It identifies the ordered rational \(2\)-torsion and has
\(j^\sigma=-j\), where \(\sigma\) is the nontrivial automorphism of
\(K\). A known rational point \(P\) of \(F\) has the same full
Kummer class as some \(Q\in F'(\mathbb Q)\) if and only if it is
the additive trace of a point of \(F(K)\); the statement also
holds over every completion, interpreting a split extension
as an étale product. To see this in a nonsplit field, choose
geometric halves \(P=2D_1\) and \(Q=2D_2\). The identical
Kummer cocycles in rational \(2\)-torsion imply
\(U=D_1+j(D_2)\) is fixed over \(K\) and
\(\sigma U=D_1-j(D_2)\), giving trace \(P\).
Conversely if \(U+\sigma U=P\), take
\(Q=j^{-1}(U-\sigma U)\in F'(\mathbb Q)\). A half of it is
\(D_2=j^{-1}(U-D_1)\). For an automorphism fixing \(K\) its
difference cocycle is minus the cocycle of \(D_1\), hence equal
in \(2\)-torsion. For an automorphism lifting \(\sigma\), using
\(\sigma U=P-U\) and \(j^\sigma=-j\) gives again the same cocycle.
For a split étale extension every point is a trace and the
twists are locally isomorphic. This proves exact both-direction
matching in the ordered classes, not merely a rank implication.

Let \(L\subseteq F(\mathbb Q)\) be the everywhere-local traces.
Doubles are global traces. The local admission of \(P\) and the
two residue exclusions give
\[
                  L/2F(\mathbb Q)=\{0,P\bmod2F(\mathbb Q)\}.
\]
In fact \(P,T_0,T_n\) generate the known quotient, and a class
with a nonzero torsion component could be in \(L\) only if
its torsion component were in \(L\) (subtract \(P\) if needed).
As the kernel of trace is the anti-invariant subgroup
\(jF'(\mathbb Q)\), trace induces the exact isomorphism
\[
 \frac{F(K)}{F(\mathbb Q)+jF'(\mathbb Q)}
 \ \cong\ 
 \frac{\operatorname{Tr}_{K/\mathbb Q} F(K)}{2F(\mathbb Q)}.
\]
Indeed if \(\operatorname{Tr} U=2V\), then \(U-V\) is
anti-invariant. This proves the index belongs to \(\{1,2\}\)
without any assumption on the anti-invariant rank. It equals
two exactly when **the known point \(P\) is a global trace**,
equivalently when this full ordered companion class is rational.

The missing arithmetic is a global \(U\), or a proof that
\(P\) is not a global trace. No such point or obstruction is
proved here. Neither the truth nor failure of this one class
decides other possible second Kummer slots on the raw companion,
different free twists, or any other literal detector.

The local p=61 ladder, first point identities and the two
finite-field halving tests replay with the Python standard
library. The earlier proved \(p^2\) source values at the two
ramified places and the first rank-one basis are cited exact
inputs, not purported outputs of this smaller checker.

~~~sh
sha256sum -c SHA256SUMS
python3 -B replay_literal_trace_index.py | cmp - EXACT-LITERAL-TRACE-LOCAL-ROWS.json
~~~
