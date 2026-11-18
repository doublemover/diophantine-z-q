# Exact constant-DVR comparison for 16 even-last successors; eight terminal split cases

Use the 24 representatives, unramified ratio scope, integral Möbius comparison and true ordinary blowup charts of RAMIFIED-DYADIC-PREFIX24. Here j=0, k=1 or 2 is the other majority index, m the minority. Our 16 representatives are in its h₀=3 branch and we start at its final sole origin w=S=0,A=1,B=0 with u=w³S, A=h/w³, B=l/w³. We obtain a single exact simpler presentation, and completely resolve eight of the 16 (the square-splitting case below), without claiming resolution of the others in this note.

## The hidden norm over an actual étale chart, not a ramified coefficient base change

The actual equations are
    A²+SA=H₀/f³,   f B²+w S B+S²=M₀ w²/f⁴,
    w²=2f,   f=f₀+ad w⁶S²,    f₀=a(e₀−e₃).
Set K=−M₀/H₀, Λ=2K−1, C=2K(K−1). Explicitly K is either 2401 or its inverse in the old contacts, or 35/3 or its inverse in the transformed contacts. Thus v₂(K−1)=5 and v₂(C)=6. A is a unit. Let
    Y=S/A+2K=Λ+H₀/(f³ A²),  X=(w B+S)/A, z=(X−Y)/w=B/A−wK/f .
The last expression is integral. Expanding the B equation using w²=2f gives (w B+S)²+S²=4M₀/f³. Completing the square with A²+SA=H₀/f³ gives X²+Y²=4K(K−1). With X=Y+wz this is exactly
    f z²+w Yz+Y²=C .
All substitutions for the last variable are invertible with unit slope; the expansions can be reversed by canceling nonzerodivisor scales. Equivalently both single-variable polynomials are transformed into each other up to the leading unit explicitly determined by B/A. No new rational split coordinate has been assumed integral here.

Now adjoin ρ=1+2h with ρ²=f/f₀, via h²+h=(f/f₀−1)/4: the RHS is integral since w⁶=(2f)³, and the derivative modulo 2 is 1. Invert ρ near the origin and put π=w/ρ, A'=ρ³ A, z'=ρ z. Then π²=2f₀, and writing O=D[π]/(π²−2f₀) for the ramified coefficient DVR (D=Z_(2), also allowing an existing unramified constant extension localized above 2), we now have
    S*=ρ³ S=(H₀/f₀³−A'²)/A',    Y=Λ+H₀/(f₀³ A'²),
    f₀ z'²+πY z'+Y²=C .
This identifies the actual chart after the original finite étale adjunction with an étale extension of this explicit O-model: over the latter adjoin h with h²+h=ad π⁶ S*²/(4 f₀), set ρ=1+2h, and recover w=πρ, S=S*/ρ³, A=A'/ρ³, z=z'/ρ. Indeed w⁶S²=π⁶ S*² exactly so these constructions are inverse on both algebras. Localize only at the units already specified. The two h-residue labels are étale comparisons, not extra geometric points in the original normalization. In particular we do not infer smoothness of a wild quotient from smoothness after extending constants by O. Rather the two charts have a common *étale* neighbourhood identified by formulas in both directions. This construction works for all 16 cases.

Set b=z'−Y, L=1+π, J=(f₀+1+π)/π (integral, a unit at 2), C=D₀π¹² for a constant odd unit D₀=C/(2f₀)^6. The equations now take the especially simple form
    f₀ b²+π L Y b+π J Y²=D₀π¹²,   Y=Λ(1−Γ/A'²),  Γ=−H₀/(Λ f₀³).
They retain the actual coefficient relation π²=2f₀.

## Eight split-contact cases, Γ≡1 modulo 4

Take γ²=Γ via the unramified quadratic using (1+γ)/2 or an existing root in the split case. Computation on the original or transformed *working* signs d,a shows this is exactly d=−a in the old contacts and d=a in the new contacts, for either k. Thus eight of the 16. Let p=A'−γ and E=Λ/A'². At the origin p=b=π=0, Y=E p(p+2γ). The actual base O[A'±] is regular with parameters π,p. We use the following two **normalized** blowups, both at the true remaining reduced point; ordinary division by an extra scale is not presumed.

For n=1,2 on the π side put p=πⁿP, b=π^(2n)B,
    y=Y/π^(2n)=E P(P+π^(2−n)γ/f₀),
    f₀ B²+π L yB+π J y²=D₀ π^(12−4n) .
For the chart at n=1 start directly with old p,b. For n=2 start with P_old=p/π and B_old=b/π². The old y has order at least two at the old origin in either step. Hence the initial square of old B (or b) is zero in the tangent cone and π and the old P directions cover the actual reduced-point blowup. Adjoining the one extra divided scale for the old B gives the displayed new monic over the regular base blowup, finite over its native ordinary blowup ratio algebra. On the other side s=P_old (p at n=1), π=sR, adjoining B_old/s² gives the monic
    f₀ Z²+sR L y_s Z+sR J y_s²=D₀ s^(12−4n) R^(16−4n),
    y_s=E(1+sR²γ/f₀)  (n=1),    y_s=E(1+Rγ/f₀)  (n=2).
Indeed y_s is the old Y-scaled function divided by s². At R=0 it is a unit, so at s=R=Z=0 the tangent conic is Z²+sR, smooth; one ordinary blowup resolves that side node. R≠0 overlaps the π side. In both new charts the monic is free over the actual regular base blowup so saturation/inverting the scale identifies it as a subring of the original function field; the extra generator is integral and contains the old ratios. On the π line B=0, with nonzero linear π in the equation if y≠0. For n=1 the only possible main origin is P=0; its quadratic B² is repeated and it is singular. For n=2 the only main origins are P=0 and P=1, where y is a regular parameter together with π (its exceptional polynomial has simple zeros). All nonregular points are therefore isolated, hence the complete-intersection finite extensions are normal by R₁/S₂ and equal the normalized ordinary blowup charts. Including the common étale comparisons does not change these local conclusions.

At each of the last two geometric points the exact equation in parameters of the regular base π,y and one new B is
    f₀ B²+π L yB+π J y²=D₀π⁴ .
First blow up the reduced origin with π,y directions (B² forces coverage). On π side y=πP,B=πV gives
    f₀ V²+π L PV+π J P²=D₀ π² .
Only P=V=0 is singular along the exceptional line: if P≠0, the linear π coefficient is a unit. On y side π=yR,B=yZ gives f₀ Z²+yR L Z+yR J=D₀ y²R⁴. At its nonoverlap R=0 the origin has smooth conic tangent Z²+yR, resolved in one ordinary point blowup.

Blow up the main π=P=V=0 point, again on π,P directions. On the π side put P=πQ,V=πW. Then
    f₀ W²+π L QW+π J Q²=D₀ .
On the exceptional line W=1; shift W=1+v. The π-linear term reduces to Q+Q² (the odd-rational f₀−D₀ is in (π²), J,L reduce to 1). At either simple exceptional root Q=0 or 1 this yields the smooth tangent conic v²+π z+λπv+μπ² in parameters π,z=Q−Q₀,v: the z coefficient shown follows from derivative 1 of Q+Q². The πv coefficient can differ at the two points. Both nodes resolve by one ordinary blowup, and elsewhere along the line the total space is regular. On P side π=PR,V=PZ gives f₀ Z²+PR L Z+PR J=D₀R². Shift Z by R if desired: at the corner the full tangent form f̄₀ Z²+PR J̄−D̄₀ R² is already a smooth conic (partials force R=P=0, then Z=0). One ordinary point blowup resolves it. Other directions on the P side overlap the π chart. All ordinary stages above are true ratio rings: use unit-leading monicity and scale nonzerodivisors for the finite covers over regular base blowups, and the ambient nonzero-divided-equation test for each conic. Since the base parameters include y near each simple root these are the genuine regular base charts there, even when the displayed formulas are only étale local coordinates, not an isomorphism to a polynomial line.

This resolves every exceptional direction of the last eight origins chosen above; in particular the Y-factorization is **exact** after the stated étale charts, not a reliance on a finite 2-adic approximation. At each round one may blow up the whole reduced singular union, including the transient conic nodes alongside any persisting main points. When a normalization is used, components of such disjoint centers at which an ordinary blowup is already regular are not modified by it. That recipe is intrinsic and commutes with all preceding étale comparisons, including normalization by finite excellence and regular base change. Consequently the construction descends even if some pairs of roots are conjugate in unramified scalar twists. The odd-prime model and the already resolved off-origin dyadic points join as in PREFIX24 and the prior D(2) construction, yielding a proper birational flat regular model of the original X_q over all Z for these eight classes and their unramified scalar variations. No claim of terminality for Γ≡3 here, nor semistability, minimality or a Lean theorem.
