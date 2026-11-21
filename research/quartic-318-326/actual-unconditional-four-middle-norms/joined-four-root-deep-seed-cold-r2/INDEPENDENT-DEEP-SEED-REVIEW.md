# Independent cold review: four middle norms and the actual deep local guards

**PASS, exact paper construction.** The author manifest is
fd80d2951a7bef3616a5d779a686c15f3935d9f0f03ebc19776a5d05ba8cb8c9
and the note is
b78155c4c6b711ab42b23a920cb674f2cf5cae4a4da8ce5f3a5688098c23f1d6.
The predecessor manifest is
6be8b5ea8d43a3d96c3767dd0bb6375ddf47a27539a12a10a835c150762247bf.
I authenticated the frozen bytes and matched both exact Python Fraction
replays. I independently substituted the explicit donor point in the
literal cubic at \(\lambda_1=41/32\) and
\(\lambda_2=1275400596441/7626746323592\). On the integral scaling by
\(d=7811144\), I obtained \((A,B,A-B)\equiv(11,10,1)\bmod71\),
\(\Delta\equiv54\bmod71\), and valuation triple
\(v_{71}(X,Y,X/Y)=(-2,-3,1)\). Thus the point is nontorsion by the
torsion-free good odd formal group, independent of any rank routine.

The first step multiplies on this fixed donor curve. Compactness
and an open integral formal subgroup give finite local quotients at
every specified prime, including bad places. One even multiple
enters all the subgroups. Subsequent powers of each residue prime
raise its depth without lowering the others. For individual exact
dyadic depths it is sufficient first to enter formal depth at least
2, where [2] raises the depth by exactly one; the required lower
bound 600 needs only strict growth. The even multiplicity makes
all three rational Kummer coordinates squares. Taking their
rational square roots gives one deep rational \(W_*\) that lies on
both parameter conics. No prescribed contact is imposed in this
first step.

On the **different**, varying-parameter curve, the two rational
parameter conics allow independent finite and real approximations.
At a retained odd \(p\), write \(D=-v_p(W_*)>0\) and take \(N>D\).
The two prescribed locally square scales of depth \(2N\) give
the good scaled model \(\tilde x=p^{2N}W^2\), with nonzero distinct
constant shifts \(1/2,1/8\bmod p\). The rational seed and target unit
cell both lift. Their translation by \(T=(0,0)\) has formal depths
\(N-D,N\) respectively: the translated parameter is
\(-\tilde x/\tilde y\). The formal logarithm ratio has valuation
\(D\), an admissible odd-prime congruence on the common multiplier;
oddness fixes \(T\). At the eight disjoint small places the
multiplier is a unit and preserves the already negative \(W\)
annuli. CRT gives one progression, not one multiplier per cell.
At infinity the same nontorsion point lies on the identity circle,
and the progression is dense, allowing arbitrarily large \(W>0\).

The two pair products are literal norms. Splitting each into
individual norms is valid: an odd inert prime not in the fixed
exceptions cannot hit both roots in one pair, and the pair
differences are \(1/2\) and \(-3^2 5^2 7^3/(407\cdot2399)\).
The imposed odd guarded poles already dominate all exceptional
denominators and differences. The full real and norm assertions
do not borrow a global rank/weak approximation theorem for an
elliptic curve.

This is the same repaired \(J,h\) and the same 19 original
**squared** cell values. The previous author trace proof
9024fb68… / 7d32108f… applies to deeper W at 2 and 3;
at 17 all three scales are units, the unweighted coefficients
are integral, and deeper W improves the weight inequalities.
For these same original poles the three-by-three \(2,3,17\) local
square conditions and prescribed minimum depths therefore hold.
This does not assert preservation of the old complete global
\(a,b\) classes, control the remaining split-order contacts or
the eight factors on the exterior scales, supply the full square
denominators or any rational PointPair, or expand the resulting
large rational W. No Lean run or remote write.

Signed: independent reviewer, 2026-11-21 UTC.

Display-only binding, independently checked: author r2 manifest
a60f3755842aad162ae0153ea5f59303e58228cb7179897ea0c60914eb58aba7,
clean note
a7d8a149ca30c967b4c82be69dcd8802a88ac3897aa8f48587d3681a56364f98.
The source checker and archived JSON are byte-identical to r1; the
r2 replay matches exactly. I reviewed the author diff: TeX delimiter
and control-character restorations do not change the proof. The
initial formal-depth-at-least-2 clarification in this receipt applies
unchanged to both display versions.
