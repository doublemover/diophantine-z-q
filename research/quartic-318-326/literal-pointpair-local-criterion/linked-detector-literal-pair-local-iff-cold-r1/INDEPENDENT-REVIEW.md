# Independent exact local PointPair review

Reviewed a81b545e97e70ef711823d5c61794ebe4ebc4ced4d853d77bee0d4758cfdecce
under manifest 11be0d7e9520248efbd80ba7535b97f2114bb93c9e9c30b741e37503108d9dcb.
All source checksums and the exact finite phase replay passed.
Independently compared the literal NormalizedPolePoints318.PointPair
type, including \(s\ne0\), with the paper's variables.

For \(B=17b,V=B^2(1-b/17)\), exact inversion is
\(P=Bt, y_1=B X, y_2=B s Z\); no change of model.
In the unit-normalized second equation the inverse is
\(s=\gamma z,\ y_2=B\beta\gamma^3 zY\), since \(Z=\beta\gamma^2Y\).
There is no omitted square scale or sign. When \(k=v_p(b)\)
is odd negative at \(p\ge5,p\ne17\), the first equation forces
\(t\) a unit, and \(v_p(tV)=3k\) then differs from the even
\(v_p(s^2)\). The two second factors share the strict minimum,
cannot vanish, and the leftover \(B\) has odd valuation.
This excludes even literal torsion-ordinate solutions.

Conversely, if \(B\) is a square, nonzero t near zero preserves
both literal squares. If \(V\) is square, using \(s^2=V\)
gives exactly \(y_2=s^3y_1\), and the first RHS has simple
zero at 1 with derivative \(-4B\). A tiny nonzero first
ordinate and near-1 parameter therefore exist at every local
field of characteristic zero under this phase. If \(v_p(b)=0\)
and \(V\) has positive depth, \(B\equiv17^2\bmod p\) is square;
hence the unit normalization in the remaining nonsquare phase
has no missed depth case. At 5 the actual branch \(z^2=-3v\)
is split and simple (derivative \(2u z(-4v)\ne0\)); at 7 the
RHS for \(z^2=3v\) is the nonzero square \(12uv^2\). For
\(p\ge11\) the genus-one Hasse bound exceeds the four points
over zero and infinity. The branch, if chosen, is again
simple. An open second square neighborhood at \(t=1\) then
accepts the same nonzero first ordinate constructed by inverse
function at \(t=1\).

The stated depths at 2,3,17 ensure \(1-b/17\) is a square
unit, and real \(b>0\) makes \(B\) square. Thus the claimed
everywhere-local equivalence with square reduced denominator
is exactly within those small-place hypotheses, not a blanket
all-place b-value square or a rational-point theorem. In
particular this is compatible with \(v_{415721}(b_{241})=1\)
and rules out the exact negative odd \(94547,699211\) rows in
the distinct arithmetic construction with those guards.
No Lean run or global realization is claimed.

Signed: independent cold reviewer, 2026-11-21 UTC.
