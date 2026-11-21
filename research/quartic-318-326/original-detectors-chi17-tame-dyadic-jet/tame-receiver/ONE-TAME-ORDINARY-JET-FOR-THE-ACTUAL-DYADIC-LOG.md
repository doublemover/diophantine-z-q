# The dyadic log needs a single tame class-polynomial jet

This refines the [actual half-orbit logarithm readout](../original-detectors-chi17-dyadic-jet-receiver-r1/DYADIC-JETS-FOR-ACTUAL-GENUS-HALF-LOG.md).
It gives one exact lower-level input and a complete ordinary
dyadic calibration at the reference \(D=-119\). The reference
is not an original detector discriminant. No tame mod-2 CM
packet or jet is supplied for either actual selected arm.

## 1. No cusp jet or leading coefficient is needed

In the prior note take the unit dyadic arm, \(X\) its exact level-48 chart
coordinate, \(B=X^4-1\), and
\[
 x=X^2+\sum_{\ell\ge1}(-1)^{\ell-1}C_{\ell-1}4^\ell
                  X^{4\ell-2}B^{-(2\ell-1)},\qquad
 y=(X-X^{-1})x .
\]
At every finite precision this has \(x\in X^2\mathbf Z_2[X,B^{-1}]^\wedge\),
so \(y\) too is regular at \(X=0\). Both expansions have controlled
pole at infinity term by term: \(x=X^2+O(X^{-2})\) there,
\(y=X^3-X+O(X^{-1})\). The prior duplication denominator
\[
 D_0=8y^4-4(3x^2-4x-3)xy^2+(3x^2-4x-3)(x^2+3)^2
\]
has leading coefficient \(8-12+3=-1\) at degree 12.
The comparison \(D_0/B^3-1\), whose coefficients are divisible by 2,
is bounded at infinity, so each geometric term of the inverse of
\(D_0\) has growth at most \(X^{-12}\); at zero it is regular.
The numerator of \(W=z(2\phi)/2\) has degree at infinity at most 11
and is regular at zero. Thus all finite logarithm approximations
are proper at infinity, and their only poles are at \(B=0\).
The same cost bound gives
\[
 L_k(X)\equiv C(X)/B^{24k}\pmod{2^k},\qquad \deg C<96k .
\]
The prior residue lemma now needs only the marked genus-half
class polynomial modulo \(B^{24k+1}\), not any cusp or leading jets.

## 2. Move the one pole to the tame level-3 variable

Use the first, ordered maps of
[Colò, Appendix A, pp. 244–247](https://www.leonardocolo.com/documents/thesis/PhD_Thesis.pdf).
For the same \(y_{48}=X^2x\), put
\[
 \begin{split}
 x_{24}&=(X^2+y_{48})/X^2=1+x,\\
 y_{24}&=(X^2y_{48}+3X^2+y_{48}^2-y_{48})/(X(y_{48}-1)),\\
 t_{12}&=y_{24}/(x_{24}-2)-3,\qquad
 t_6=t_{12}^2/(t_{12}+2),\\
 u=t_3&=t_6^2(t_6+9)/(t_6+8)^2 .
 \end{split}
\]
These forget the 16-flag and keep the same selected 3-subgroup.
Modulo 2, the branch \(y_{48}\equiv X^4\) gives
\(x_{24}\equiv1+X^2\), \(y_{24}\equiv X(X^2+1)\),
\(t_{12}\equiv t_6\equiv X+1\), hence \(u\equiv X\).
The \(X\) in the denominator of \(y_{24}\) cancels:
the numerator is divisible by \(X^2\) exactly.
All remaining denominators are units modulo 2 after inverting \(B\).
The supersingular point is removed, in particular \(u-1\) is a unit.
The defining series in §1 are evaluated modulo each finite precision.

At zero \(x_{24}=1,y_{24}=0,t_{12}=-3,t_6=-9,u=0\).
At infinity \(x_{24}\sim X^2,y_{24}\sim X^3\),
and each of \(t_{12},t_6,u\) has leading term \(X\).
These bounds hold coefficientwise in the 2-adic expansions:
for series at infinity, factor the leading Laurent power
before inverting each denominator with unit leading coefficient.
In the completion of \(\mathbf Z_2[u,(u-1)^{-1}]\) solve \(u=u(X)\)
by \(X_0=u,\ X_{j+1}=u-(u(X_j)-X_j)\). Each step improves by one
bit, since \(u(X)-X\) is 2 times a function in the corresponding
localized ring and all substitutions have \(X_j\equiv u\bmod 2\).
This is the unique branch with that reduction. Each iterate is
regular at zero, has leading term \(u\) at infinity, and is ordinary
away from \(u=1\). Consequently \(L_k(X(u))\) is a proper rational
function modulo \(2^k\), with denominator a power of \(u-1\).
It can be written \(A(u)/(u-1)^M\), with \(\deg A<M\);
the finite ring computation determines a sufficient \(M\).

Let \(F_+(u)\) be the monic product of the *actual* selected tame
level-3 \(u\) values in one genus half at the chosen local embedding.
The named genus fields split at 2, so the decomposition group in
the full Hilbert class field preserves the chosen half, not necessarily
every individual class. All \(u\) are integral and avoid 1 modulo 2.
Consequently the trace of the logarithm approximation is
\[
 -[(u-1)^{M-1}]
   \big(A(u) F_+'(u)/F_+(u)\bmod (u-1)^M\big).
\]
It needs one jet, \(F_+\bmod(2^k,(u-1)^{M+1})\), with no
denominator or discriminant singularity. The same method with
the whole oriented product, rather than the half, gives the
unweighted raw logarithm directly. Neither receiver supplies
its CM polynomial input.

## 3. Higher bits follow uniquely from ordinary marked mod-2 data

Suppose an ordinary mod-2 value \(u_0\ne0,1\) from the **correct
oriented** tame packet is supplied in \(\mathbf F_{2^f}\); work in
its unramified lift with Frobenius \(F\). The tame source and target
invariants are
\[
 j_s(u)=\frac{(u+27)(u+243)^3}{u^3},\qquad
 j_t(u)=\frac{(u+27)(u+3)^3}{u}
\]
and \(j'_s(u)\equiv (u+1)^4/u^4\) modulo 2. In particular,
given the canonical lift \(j\) of \(j_s(u_0)\), there is a
unique Hensel lift of the selected 3 flag from \(j_s(u)=j\).
This uses the tame étale flag, not a choice from unordered
\(j\)-neighbors.

For \(j\) a unit the unique unit solution \(t\equiv j\bmod2\)
of \(j=(t+256)^3/t^2\) exists by Hensel, with unit derivative.
Set \(J_2(j)=(t+16)^3/t\), the canonical 2-quotient on
this branch, reducing to \(j^2\). On the ordinary modular
components the unit \(t\)-branch has first map identity
and second map Frobenius, hence the connected 2 subgroup;
the reversed branch has the opposite order.
The map \(j\mapsto F^{-1}J_2(j)\) fixes the residue and
contracts by one extra bit at each step (the derivative of
\(J_2\) is zero mod 2). The actual maximal CM lift satisfies
this fixed point because the local CM order is split and
the chosen 2-subgroup is canonical. Thus its unique solution
is the indicated canonical \(j\) modulo any prescribed \(2^k\).
No additional high-precision oriented CM data are required
once the genuine mod-2 packet or an adequate aggregate is
supplied. This does not find that packet.

## 4. Complete D = -119 dyadic calibration

Here \(h=10\), with a class above 2 of order five and a
class above 3 of order ten. By the norm-36 relation in the
[odd-weighted reference calculation](../original-detectors-chi17-reference-parity-r1/EXACT-D119-WEIGHTED-SEED-IS-ODD.md),
choose the 3-arm with square equal to the square of arithmetic
2-Frobenius in the class action. The coarse ordinary \(\pm1\)
automorphisms do not interchange two different cyclic 3
subgroups. The ordinary tame \(u\) values lie in \(\mathbf F_{32}\).
Two successive 3 edges from \(u\) move
\(u\to v\to u^4\), where \(j_t(u)=j_s(v)\),
\(j_t(v)=j_s(u^4)\) and neither transition reverses
the chosen edge. Reversal at this prime is \(w_3(u)=1/u\).
The fixed finite table gives exactly ten \(u\) values with
one such \(v\) each, in two Frobenius orbits of five,
interchanged by this successor. At least one is an actual
CM residue, and Frobenius and the unique successor then give
all ten distinct marked labels. No CM class polynomial is
used, and this accounts for all multiplicities.
These are the two \(\chi_{17}\) halves because the
Frobenius has sign plus and the 3 successor has sign minus.

Lift one representative per orbit by §3 over
\((\mathbf Z/2^{14})[S]/(S^5+S^2+1)\). Lift arithmetic
Frobenius by its unique root over \(S^2\bmod 2\).
Take \(X\) by the ordinary inverse of §2, evaluate
\(\tfrac12\log(z(2\phi))\) on the literal model, and use
the unramified ring trace of each value. Up to exchanging
the halves, the exact residues are
\[
 (\log A_+,\log A_-)\equiv(264,11824)\pmod{2^{14}},\qquad
 \log P\equiv12088,\quad\log R\equiv4824 .
\]
Their depths are \(3,4,3,3\), respectively.
The weighted depth agrees with the independent odd free
coordinate and the exact depth-three generator logarithm.
If the reference unweighted trace were torsion then
\(2\log A_\pm=\pm\log R\) would force depth 2 on both halves,
which fails. This is a separate exact dyadic nonvanishing
test for the genuine **reference** trace only; the reference
also had earlier inert-prime certificates.

The executable canonical lifting, tame inversion and
logarithm run in under one second for the two degree-five
reference representatives, using only the Python standard
library. This speed says nothing about finding the actual
detector's much larger oriented ordinary packet. Ordinary
canonical CM lifts do not give a way to replace their coarse
residual labels by just genus reciprocity or by valuations
of singular moduli. Evaluation of the one jet (from an
exact marked mod-2 aggregate or another theorem) remains open.

## Replay

Run \(\texttt{python3 -B replay_D119_dyadic_tame_lift.py | cmp - EXACT-D119-DYADIC-TAME-LOG.json}\)
and \(\texttt{sha256sum -c SHA256SUMS}\).
