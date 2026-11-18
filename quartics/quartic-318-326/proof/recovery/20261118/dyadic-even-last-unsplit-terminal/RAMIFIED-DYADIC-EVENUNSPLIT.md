# Eight remaining unsplit close-contact cases: cusp after the quadratic cancellation

Use the exact common étale O-chart of RAMIFIED-DYADIC-EVENCLOSE, with π²=2f₀, Λ=2K−1, L=1+π, J=1+(f₀+1)/π, Y=Λ(1−Γ/A'²), D₀=2K(K−1)/π¹² an odd rational unit. Here Γ≡3 modulo 4: **no** étale square root of Γ is assumed. These are the remaining eight of the 24 PREFIX24 cases (pair 01 or 02, d=a for the old contacts or d=−a for the new working contacts). We calculate all remaining charts. The ambient base from now on, until a base blowup is specified, is the regular O-line with coordinate A' localized at its origin A'=1,π=0. We always retain the formula π²=2f₀.

## Passing to the triple intersection

Put p=A'−1, E=Λ/A'², c=(1−Γ)/(2f₀), k=(1+c)/2. Both c and E are units; c is odd so k is integral. Then Y=E(p²+2p+2 f₀ c). The old equation is f₀b²+π L Y b+π J Y²=D₀π¹². Blow up the reduced point π,p,b and normalize; the π,p directions cover because Y∈(π,p)² and the square of the initial b vanishes. On the π side p=πP, b=π²B (one extra integral scale), y=Y/π²=E(P²+(π/f₀)P+c), giving
    f₀ B²+π L y B+π J y²=D₀π⁸ .
At π=0 only P=1 can be bad since otherwise y≠0 and the π-linear term is nonzero. On the p side π=pR, b=p²Z, y_s=Y/p²=E(1+pR²/f₀+cR²) and the corresponding equation is f₀ Z²+pR L y_s Z+pR J y_s²=D₀ p⁸R¹². At R=0 the tangent conic is Z²+pR at its sole origin; resolve by one ordinary blowup. Both presentations are free monics over regular base charts, contain the ordinary ratios and are finite over them; they are normal since bad only at isolated points. Their scale inverses restore the original ring, hence they are exactly the true chart normalizations.

Near P=1 write q=P−1, so there is an *exact* equality
    y=E(q²+π H),    H=(1+q)/f₀+π(q+k)/f₀ .
The reduced origin is π=q=B=0. Blow it up ordinarily with π,q directions (if both zero then the B tangent square is zero). On π side q=πQ,B=πZ the equation is f₀ Z²+π L (y/π)Z+π J(y/π)²=D₀π⁶. Here y/π is a unit at every point on the exceptional line, so this whole side is regular. On q side π=qR, B=qZ and set
    D=y/q=E(q+R H).
The equations are
    f₀ Z²+qR L D Z+qR J D²=D₀ q⁶R⁸ .
Outside R=0 directions overlap the π side. At R=q=0, Z=0 is the only point, and is nonregular (order-two relation in regular ambient q,R,Z). The monic presentations are saturated and give the actual ordinary blowup, already normal.

Next blow up that reduced point and normalize. The q,R directions cover by the quadratic; on the q side R=qT, D=qD', D'=E(1+T H), Z=q²V with one extra integral division. We obtain the exact equation
    f₀ V²+qT L D' V+T J D'²=D₀ q¹⁰T⁸,   π=q²T .
Along the exceptional divisor D' reduces to 1+T since H=1/f₀ and E=1 in the residue. Its reduced equation for V is V²=T(1+T)², which is regular away from T=1 by its T derivative (no restriction to rational directions). On the R side q=Rs, D=R D'', D''=E(s+H), Z=R²V'. The equation is
    f₀ V'²+Rs L D'' V'+s J D''²=D₀ R¹⁰s⁶ .
At s=0 the divisor equation has unit derivative in s since D'' is a unit, so the new side is regular; nonzero s overlaps the preceding chart. Both finite monic extensions are actual chart normalizations, by the same unit-leading, scale-inversion, and isolated-bad-point R₁/S₂ argument. One singular point T=1,V=0 remains.

## The cancellation responsible for the cusp

Put t=D'. The base O-chart at q=0,T=1 is a regular local surface with parameters q,t: modulo q we have exactly t=1+T; E and H restrict to 1 there. Write v=V−t, M=T L, N=f₀+T J+qT L, U=D₀T⁸. Thus
    f₀ v²+q M' t v+N t²=U q¹⁰,   M'=M+q³T² a unit.
The extra term of the v-coefficient comes from 2f₀=π²=q⁴T². We need the stronger membership
    N=B₀ t+q² B₁,     B₀ a unit, B₁ regular .
Indeed in the quotient by t we have T=−1/H. Since π=q²T and H≡(1+q)/f₀ mod q², J,L≡1 mod q²; hence N≡f₀−(1+q)/H≡0 mod q². This proves membership in (t,q²). The coefficient of t is a unit because N restricted to q=0 is f̄₀+T=1+T=t. No need to invert q or t or divide them in the regular local ring. The discarded linear-in-q contribution cancels; forgetting it would give a different singularity. We have now proved the exact local equation
    f₀ v²+q M' t v+(B₀ t+q² B₁)t²=U q¹⁰
in regular base parameters q,t, with M',B₀,U units. Coefficients in all further substitutions are actual pullbacks, not new unrelated constants. The original point is singular since there is no linear part.

## Four further true point blowups (one normalized)

First blow up the origin with q,t directions; the tangent square v² forces coverage. In the t direction q=tR,v=tZ the equation is
    f₀ Z²+t R M' Z+B₀ t+t²R²B₁=U t⁸R¹⁰ .
The t-linear coefficient B₀ is a unit on its exceptional line at Z=0, so the entire side is regular. In the q direction t=qS,v=qB it is
    f₀ B²+q M' S B+q B₀ S³+q² B₁ S²=U q⁸ .
At S≠0, the q-linear coefficient is nonzero, so only the S=0 closed origin can remain, and is singular.

Second blow up this origin, normalizing. The q,S directions cover by the same quadratic. On q side S=qP,B=q²Z adjoin one integral extra scale and obtain
    f₀ Z²+ M' P Z+B₀ P³+B₁ P²=U q⁴ .
At P≠0 this is étale in Z on the divisor and at P=0 only Z=0 occurs, a singular origin. On S side q=SR,B=S²V the equation is
    f₀ V²+R M' V+R B₀+R² B₁=U S⁴R⁸ .
At R=0 the R-linear coefficient B₀ is a unit and gives regularity; R≠0 overlaps. The new rings have one monic over the regular base blowup, are finite over the ordinary ratios and include them. Inversion identifies the fraction field, and complete intersection plus isolated nonregularity implies normality, hence exactly the claimed normalized blowup.

Third, blow up the main q=P=Z=0 point. The q,P directions cover using the equation's tangent form (which can have P Z and P² terms). On q side P=qW,Z=qV:
    f₀ V²+M' WV+q B₀ W³+B₁ W²=U q² .
On W≠0 the V derivative is a unit; W=0 gives just the singular origin V=0. On the P side q=PR,Z=PZ' the equation is f₀ Z'²+M' Z'+B₀P+B₁=U P²R⁴, étale in Z' along the divisor since M' is a unit from the base. The ordinary charts are already normal.

Finally blow up q=W=V=0. On q side W=qR,V=qZ the equation is
    f₀ Z²+M' RZ+q² B₀ R³+B₁R²=U .
On q=0 all coefficients M',B₁,U reduce to constants (functions pulled back from the preceding local bases at their closed origins). Its residue curve is smooth: for R≠0 the Z derivative is a unit, while at R=0 Z²=Ū/f̄₀≠0 and the R derivative is M̄'Z≠0. On W side q=WT,V=WZ' the equation is f₀ Z'²+M' Z'+W²T B₀+B₁=U T², whose Z' derivative is a unit there. The two directions cover since the old quadratic forces the V direction zero when the other two vanish. No singular point remains.

Each ordinary ratio ring just used is saturated: adjoining the single monic to the true respective blowup chart of the regular two-parameter base is free, the scale is a nonzerodivisor, and its inversion is the old localization with the explicit inverse substitution. For normalized charts the same argument after the integral extra scale, together with R₁/S₂ as verified, gives the finite integral closure. Smoothness tests on the exceptional curves imply regular total spaces because the scale is a nonzerodivisor. The isolated singularities at intermediate steps are codimension two; complete intersections and unchanged off-center normality give normality also before the subsequent ordinary steps. The separate side conic is resolved by the usual ambient nonzero-mod-scale division test. The reduced closed centers or their disjoint unions and the finite normalizations commute with the common *étale* chart identifications and unramified coefficient variations. Taking them intrinsically (blowing up any coexisting simple nodes with the main center) therefore gives these proper birational modifications of the actual X_q. The off-origin points and all odd characteristics have the previously reviewed regular models, unchanged on the common overlap. The resulting flat proper integral model is regular over all Z in these eight further classes. Taken with the separate split and pair-12 constructions this exhausts the 24 representatives in PREFIX24, but not every dyadic type. No minimality, smooth special fibre, rank or Lean acceptance follows.
