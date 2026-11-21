# Independent review: no rational section on the fixed scalar's full shift chart

**Mathematical and exact replay PASS, 2026-11-21.** This binds the
author manifest 3eb1d2208400cf4865337b80f97757cebe365c86b0bffc36b3f0359d81c80534,
manuscript 7e6655baeadfbb047cc6150bd96d3b1dc3de07b34364d9416411721ce183ea7d,
and exact controls 982d6050d0faf35d8357b1a9175dd3652ab1a8a652a230bf7ab1b66c8f2d6fe3.
I checked every author manifest entry and upstream hash and reran
`python3 -B replay_full_chart.py | cmp - EXACT-CHART-CONTROLS.json`
with byte-identical output.

The paper keeps exactly the original fixed h and second direction, and
varies the shifted point on the full Weil restriction X, not just its
shift norm. The two degree-four functions give disjoint simple zero and
pole sets on each elliptic factor and 32 transverse base points on the
product. The blow-up resolves the actual pencil; the exceptional curves
are sections. Critical points over a finite nonzero value are products
of two simple critical points, so branched base change gives only
ordinary double points. The cover of the pencil base is unramified at
zero and infinity. The Koszul computation gives h⁰(K+2F)=33, while
surface Riemann–Roch gives χ(−2F)=32 and h⁰(−2F)=0. Thus the
resolved cover has Albanese dimension three. The two invariant source
differentials and the anti-invariant trivializing-curve differential
exhibit its three factors up to isogeny, with no omitted Prym dimension.

The source factors have integral j at 3 whereas the target's
j=2048/3 is nonintegral there. The third factor has j-valuation −4 at
181, where the target has integral j. I checked the even-quartic
normalization against [Fisher, §2 (2)](https://people.maths.bris.ac.uk/~jb12407/ANTS-XV/papers/ANTS-XV_fisher.pdf);
potential good reduction rules out each geometric isogeny. Thus a
rational map from the smooth resolved cover to the constant target
curve is constant. Equivariance under the cover involution forces a
constant map arising from a section to be one of the four finite
branch points, none rational. The two points at infinity are exchanged.

Here **geometric generic** means the function field of
X after extending its constants to the algebraic closure of Q, written
Qbar(X); it does **not** mean an algebraic closure of Q(X). The four
branch points are the only Qbar(X)-points, and there are no
Q(X)-points. The separate two-residue order witness and CM conjugation
argument give Zariski density of a nontrivial progression of the
original shifts. Density and the function-field obstruction do not
settle whether the one actual shifted point admits an arithmetic point,
whether a lower-dimensional construction works, or what happens with
a varying h or second direction. No Lean compilation or remote write.

Reviewed by the independent proof/CI lane.
