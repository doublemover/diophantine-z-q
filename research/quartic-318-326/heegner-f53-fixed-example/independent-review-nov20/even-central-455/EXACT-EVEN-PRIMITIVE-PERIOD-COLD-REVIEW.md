# Independent cold check: exact primitive even central value at −455

Scope: one explicit minimal-differential, primitive-period convention
for the same \(E_{323},h_*=-455\); not a different integral Kato
lattice, the varying companion selection, or a native Lean claim.

The Fraction script
235bfdedfabcf07ff9cbf2a886b1d4986ef607edfa5b7b65623d507c2c544cb2
replayed byte-identically to
0ab3282d230b12beb385de1e5b5d105b4574da95f3c510cd312acd525e827900,
using the separately checked fixed companion L enclosure
16166f7f30dbdc04635824dbb96891acc3c295e46e3ab3892229e68ea9327dd6.
No new NTT execution was needed.

1. The literal target \(E_{-1}:Y^2=X(X+1)(X-3)\) is the listed 48a1
   model via \(x=X-1,y=Y\); this is a translation, not an isogeny
   scaling. [Brunault, §6.3](https://perso.ens-lyon.fr/francois.brunault/recherche/reg_siegel.pdf#page=16)
   identifies that modular quotient and [Martin–Ono](https://uva.theopenscholar.com/files/ken-ono/files/026_8.pdf#page=5)
   its genuine level-48 newform. The same literal map used in the
   finite evaluation has differential
   \(-(x_{48}^2+1)dx_{48}/(2y_{48}-x_{48}^4-1)\).
   At \(\infty\), \(x_{48}\sim q^{-1}\) and
   \((2y_{48}-x_{48}^4-1)/x_{48}^4\to1\), so the leading term
   is \(+dq\), not twice \(dq\). This fixes exactly \(f(q)dq/q\)
   on the one conductor-48 elliptic line. The literal discriminant
   is \(2304 n^6\). All nonzero finite valuations are below 12
   for \(n=-1,323\), so these differentials are minimal.

2. Write \(D=146965\). For every \((a,D)=1\),
   choose \(uD-48av=1\); the matrix with second column \((a,D)\)
   and first column \((u,48v)\) lies in \(\Gamma_0(48)\) and
   maps cusp 0 to \(a/D\). Thus the integer-weighted cycle
   \(\sum_a\chi_D(a)[\infty,a/D]\) is truly closed:
   all boundaries coincide and \(\sum_a\chi_D(a)=0\).
   Fourier integration from \(q=0\), with the unaveraged Gauss sum
   and the cusp Abel limit, gives period \(\tau_D L(E_{-146965},1)\).
   Its absolute value uses \(\sqrt D\), not \(\sqrt D/2\) or an
   averaging factor.

3. The real identity component gives the primitive real period,
   not the sum of periods from both components. Its exact integral
   is \(\int_3^\infty dX/\sqrt{X(X+1)(X-3)}\).
   Under \(X=-1+4/t^2\) this becomes
   \(\int_0^1 dt/\sqrt{(1-t^2)(1-t^2/4)}\), hence
   \((\pi/2)\sum_{j\ge0}\binom{2j}{j}^2/64^j\).
   Each term of the series is at most \(4^{-j}\).
   The closed cycle thus gives an integer, and the exact interval
   bounds that integer between approximately 2047.997188 and
   2048.002812. It must be 2048.

4. The literal complex twist map scales the differential by
   \(1/\sqrt{-323}\), carrying the primitive real lattice onto
   the primitive imaginary lattice of \(E_{323}\). Therefore
   \(\sqrt{455}L(E_{-146965},1)/|\Omega^-_{E_{323}}|=2048\) and
   its two-adic valuation is exactly 11 here. The manuscript's K14
   explicitly allows a fixed rational comparison for a different
   chosen lattice; the result does not assign such an independently
   fixed scalar a valuation.
