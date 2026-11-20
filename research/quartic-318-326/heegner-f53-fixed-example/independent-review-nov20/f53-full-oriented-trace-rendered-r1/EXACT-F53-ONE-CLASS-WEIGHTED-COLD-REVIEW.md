# Independent one-class F53 weighted reduction review

Frozen script dceac1e0e52aca8b80d6364cf844d6e1fb603b648b448792766b3ca0284b4690
replayed to byte-identical JSON
5fa88534c794ef93d655c8f6ef055fe92dda57ae9b0bedab3243669c73ef4dc8
(exit 0, 8.47 s). Scope: one fixed oriented class, not the full trace.

The base marked \(C_{17}\), \(C_{19}\) quotients are actual; their
composite is invertible on \(E(\mathbf F_{53^2})\) of order \(54^2\).
On this same codomain the descended degree-114 endomorphism is uniquely
identified by 229 distinct interpolation points; the cleared difference
of two candidate rational \(x\)-maps has degree at most 228. The
differential fixes the \(y\)-sign. The two residual roots at each prime
distinguish the desired actual marked and opposite lines.

For each contribution, use the actual \(Q_{17}+aP_{17}\) and
\(Q_{19}+bP_{19}\) lines, pushing both entries of the 19-basis through
the SAME degree-17 map: every outer row tests
\(e_{19}(fP,fQ)=e_{19}(P,Q)^{17}\), not independent re-normalization
at that depth. The 16-by-18 grid is exactly the unit CRT rectangle
and the product of Legendre weights is \(\chi_{-323}\).

The direct marked \(t_8\) is independently justified. In the
translated marked order-2 model, the order-4 abscissa \(v\) has \(v^2=b\).
Put \(r=x(P_8)/v,k=a/v,s=r+r^{-1}\); duplication gives
\((s-2)^2=4(k+2)\). The normalized raw \(x\)-map is \(x+b/x\);
shifting at the image of \(P_4\) changes the abscissa and quadratic
coefficient to \((s-2)v,(k+6)v\). Both resulting \(t_4\)-values match
\(t_8=32/(s-6)\) under the corrected degeneracies. At level 16, from
ordered \(t_8\) outputs \(a,b\) recover \(t_{16}=(b-2a)/(a+4)\).
The denominator is nonzero on a noncuspidal point. Independently
enumerated all 203 distinct top chart keys used by the 288 rows:
one chart each, with no \(r=0\) or denominator-zero branch. The
[moduli formulas](https://www.leonardocolo.com/documents/thesis/PhD_Thesis.pdf)
are those of Colò with the level-8 typo corrected in the earlier note.

For the summed primary basis the common phase is
\(z_{17}^{19}z_{19}^{17}\). The signed Gauss factors are \(21,4u\),
so \(s=31u\) and \(s^2=-323\). Replacing the primitive phase by its
\(k\)-th power changes the raw weighted point and \(s\) by the same
\(\chi(k)\): rescaling the two generators by units \(v,w\) with
\(vw=k\) reindexes the slope by \(v^2/k\). The matched twist cancels
that sign. It does not permit mixing independently signed raw class
rows.

Separate pair arithmetic verified all 288 weights and the raw
\(E_{-1}\) sum \((24+44u,12+26u)\). The actual \(E_{323}\) twisted
class value is \((39+45u,9+48u)\); its \([224]\)-image is the
order-13 point \((49,48)\). This is one summand, not a trace,
Artin assignment for the other rows, or rank result. No Lean was run.
