# Independent review: the literal one-I rank-zero even auxiliary

The exact paper ACTUAL-ONE-I-EVEN-CASSELSEL.md is bound by SHA-256
075362daa49e9e393af80005c9792f270929bcad3346aa206131bdb13fe26201.
The author manifest is
bfbb56c74ee41e832bf210d16605856df0283de475868da8085ae7904e608094.
The data, replay code and replay hashes are respectively
ae5f5fb98c8f3e6a735034ca8cc4a400334a12653d5375535c9d03e85ad718fc,
77b548a573afa0eefd443d950698eb7c248944ec15135150fdb364c83b5b69d9,
and 2107dd9ce03b1f7b9b00219900da1123779eb62c9f273a2baae7f57a40e6661b.
The author's output replays byte-for-byte.

**Fixed scope.** Use the existing literal
\(d=2811626664334219040035976315\), the chosen
\(m=7\cdot13\cdot19\cdot283079=489443591\), and
\(D=md=1376132651143091791135781016804547165\).
The exact curve is \(E_{-D}: y^2=x(x+D)(x-3D)\), the positive \(D\)
twist of \(E_{-1}\). The auxiliary field is \(\mathbb Q(\sqrt{-m})\),
not the two-division field of this curve and not the previously
selected compact field. Its discriminant \(-m\) is fundamental:
\(m\) is squarefree, \(-m\equiv1\bmod24\), and the four listed
primes are prime to \(6\cdot53\cdot d\). It splits all primes
dividing \(6d\) and is inert at 53, checked independently.

**Finite arithmetic.** The independent replay builds the local
square-class spaces with explicit finite square sets and separate
binary elimination. At the retained 17 places the spanning
dimensions are 1 at infinity, 3 at 2, and 2 at odd finite places
by the local point-group index and full rational two-torsion.
All other places are odd good places, and a point has unramified
Kummer labels there: negative x-valuation forces all three
coordinate valuations equal and even, whereas for integral x
the three root values are unit separated. This yields rank 30
on 34 global bits, so \(\dim\operatorname{Sel}_2=4\), with the
two literal torsion labels and the two announced \(\lambda,\mu\)
independent.

**Exact global pairing, not just local incidence.** In the
root order \((0,-D,3D)\) the class \(\lambda=(a,1,a)\) has
\(z_2^2-a z_3^2=4D t^2\) and \(z_2^2-a z_1^2=D t^2\).
The primitive seeds \((2A,2B,C)\) and \((A,B,C)\) have
exact conic equation \(aA^2+DC^2=B^2\). The polar forms are
\(aAz_3-Bz_2+2DCt\) and \(aAz_1-Bz_2+DCt\). The omitted
middle tangent contributes nothing for \(\mu=(g,1,g)\).
The [Cassels full-2-descent pairing](https://doi.org/10.1515/crll.1998.001)
therefore computes the global product of the two Hilbert symbols
against \(g\) at each place. Outside \(2\cdot3\cdot D\), the
projected triples remain primitive (if a triple vanished, the
other cover equation forces the last coordinate to vanish).
Their smooth conics have primitive tangent sections; at a
modular tangent zero the value is a unit times a squared
local parameter, and elsewhere the value is a unit. The
local symbols against unit \(g\) are thus trivial. At infinity
\(g>0\); at finite nonsquare places the independent replay uses
different Hensel lifts, verifies precision for every sign choice,
and computes the Hilbert symbol of the product via its local
bilinear generator table. Exactly \(2,5,733\) give \(-1\).

**Consequences.** The alternating pairing has rank 2, and
its entire radical consists of the two independent torsion
Kummer classes. The rational-point image is contained in the
radical and contains those classes, so rational rank is zero.
The quotient \(\Sha[2]\) is \((\mathbb Z/2)^2\) with a
nondegenerate pairing. A hypothetical element \(x\) of order
4 would have nonzero double \(2x\) orthogonal to all \(y\in
\Sha[2]\) because \(\langle2x,y\rangle=\langle x,2y\rangle=0\).
Hence \(\Sha[2^\infty]=(\mathbb Z/2)^2\) and the full
\(2^\infty\)-Selmer group has corank zero. The two-division
field is \(\mathbb Q\) itself. These are the exact hypotheses of
[Burungale–Tian, Theorem A](https://arxiv.org/html/2611.11566v1#ThmtheoremA),
a public preprint with [v1 submitted November 8, 2026](https://arxiv.org/abs/2611.11566),
so its conclusion gives \(L(E_{-D},1)\ne0\). The exact
arithmetic rank-zero proof does not rely on that preprint or
on finiteness of the whole Tate–Shafarevich group.

No central-value size, 13-adic nonzero residue, companion
support for \(d\theta\), base derivative, marked rational
point/rank on \(E_d\), or Lean theorem is claimed.

Replay:
    python3 -B check_even_independent.py EXACT-EVEN-AUXILIARY.json | cmp - INDEPENDENT-REPLAY.txt

Reviewed independently, Vesper, 2026-11-21 UTC.
