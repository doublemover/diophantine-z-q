# The complementary 24 new parity cases: two integral scales give a split, rather than a Gaussian, norm

Take the same two working contact configurations and mixed-parity arrangement as PARITY24, with an equal odd majority sign (d,d), q_m=2a, q₃=2a₃. Now require **A₀=(ad−f₀)/2 even**, i.e. f₀/(ad)≡1 mod4. This is the complementary 24 original ordered representatives (the m choices, d,a and direct/transformed configurations); none has been claimed by PARITY24. For all of them the initial half-product normalization in that packet remains literally correct: the proof used the cubic term ad u³ with coefficient odd independently of A₀ parity. We explicitly resolve every origin, with a genuine normalization at the second blowup.

Write D=e_j−e_m, M=aD/2=2⁴M₀, H=d(e_j−e_k)/4=2^h₀ H₀, C₀=(ad−a₃d)/2, f=f₀+a₃d u², and use the original integral b=((1+u)y_m−uw)/2 satisfying
    b²+w u b=M(1+u)²+u²(A₀+ad u+C₀u²),   w²=2f .
As before h²+uh=H. All constants with subscript zero except A₀,C₀ are units when previously specified; D₂=(A₀/2)/f is regular, not necessarily a unit.

## Actual preparatory charts

On the first ordinary reduced-point blowup use w,u directions. They cover by the quadratic leading relations, and the monics over the regular base blowup are the actual saturated ratios. On the w side u=ws,h=wE,b=wB:
    E²+sE=H/w²,   B²+w sB=M₀ w⁶(1+u)²/f⁴+s²(A₀+ad w s+C₀ w²s²).
For s≠0 the term ad w s³ is a unit times w and regularizes the B equation, while E is étale. For s=0 only the edim-four origin remains. On the u side w=uR,h=uE',b=uB':
    E'²+E'=H/u²,  B'²+uR B'=M(1+u)²/u²+A₀+ad u+C₀u² .
At R=0 the unit linear term ad u gives regularity. Terms H/u² and M/u² express integrally using 2=u²R²/f; A₀∈(w²). There are no side nodes at this first stage, and the ordinary blowup is normal by isolated nonregularity.

Next blow up w=s=E=B=0 with w,s directions (tangent equations enforce coverage). On the w side set s=wP,E=wE₂,B=w²B₂, one *additional integral scale* beyond B/w:
    E₂²+P E₂=H/w⁴,
    B₂²+P B₂=M₀ w²(1+u)²/f⁴+P²(D₂+ad P+C₀ w²P²),   u=w²P .
These extend the actual ordinary ratios integrally. At P≠0 both residue derivatives are units. At P=0 there is the unique edim-four origin. On the s side w=sR,E=sE',B=s²B' we have
    E'²+E'=H/(w²s²),
    B'²+R B'=M₀ s²R⁶(1+u)²/f⁴+R² D₂+ad R+C₀ s²R²,   u=s²R .
At R=0 the R derivative is the unit ad at B'=0, and E' is étale; the other directions overlap. These finite extensions are free monics over the respective regular base charts, scale localization restores the original ring, and they contain all ordinary chart generators. The rings are S₂ with only isolated nonregular exceptional primes and previously normal elsewhere, hence R₁; thus they are the actual normalized blowup charts, without pretending that B/w² was already an ordinary ratio.

Third blow up the main origin ordinarily on w,P directions. On the P side w=PR,E₂=P E',B₂=P V' the two unit-leading monics have E'²+E'=H/(w⁴P²) and
    V'²+V'=M₀ R²(1+u)²/f⁴+D₂+ad P+C₀w²P² ,
étale on the exceptional divisor (all coefficients integral including h₀=3). On the w side P=wS,E₂=wE,B₂=wV, i.e. u=w³S,h=w³E,b=w⁴V, yielding
    E²+SE=H/w⁶,
    V²+SV=M₀(1+u)²/f⁴+S²(D₂+ad wS+C₀ w⁴ S²).
For S≠0 both derivatives are units. For S=0 we have V=1 and E=0 if h₀=8, E=1 if h₀=3. These ordinary charts are again true ratio charts by monic saturation. Only this single closed point may be singular. The two case analyses identify its actual equation and show it singular (edim three), and thus the third stage already normal. The reduced centers followed are the actual unique preceding singularities.

## A quadratic-contact terminal calculation

Both cases below have the following local model in a dimension-two regular base with parameters x,p and residue characteristic 2, x²=2f for a unit f, and one monic variable A:
    A(A+t)=U x¹⁰,    t=E' ((γ+p)²−r),   E',U units .
Here r is an odd rational constant; choose γ=1 if r≡3 mod4, otherwise choose γ²=r via an **étale** (1+γ)/2. The base includes a unit f₀ such that f=f₀ modulo (t) (in the applications f₀ is an odd rational constant and f−f₀ has a factor t). No independent order for 2 is presumed. The quotient base by x is smooth in p at the origin (as it is in both verified presentations), and the true base charts are the blowups at regular parameters. Let c be the residue of (γ²−r)/(2f₀), equal to 1 or 0 respectively.

First blow up the reduced origin, whose x,p directions cover since t∈(x,p)². On x side p=xP adjoin Z=A/x² (one extra integral scale). Then
    Z(Z+t₁)=U x⁶,   t₁=t/x²=E'[P²+(xγ/f)P+(γ²−r)/(2f)] .
On the p side x=pR, Z'=A/p² the equation is Z'(Z'+t/p²)=U p⁶R¹⁰. At R=0 the coefficient t/p²=E'[1+p R²γ/f+(γ²−r)R²/(2f)] is a unit so the ring is étale there; nonzero R overlaps. On the x line only the unique root P=c has t₁=0 and can be singular, since outside it Z's derivative is a unit. These monics are finite over the ordinary ratios and contain them, coincide off scale, and are normal by complete intersection and isolated bad directions; hence the claimed finite chart normalizations.

For c=1 put s=P−1. On the actual x-chart quotient by t₁=0 we have t=0, f=f₀, x²=2f₀ and
    P²+(x/f₀)P+(1−r)/(2f₀)=0 .
Thus t₁ has unit x-linear term up to its unit factor (the last constant odd, f−f₀ divisible by t=x²t₁). In the regular base x,s this yields a DVR after setting t₁ to zero and x∈(s²). Since 2∈(s⁴) in this quotient, the exact relation gives x≡s² modulo s³; in particular the order is exactly two. In the regular ambient adjoining Z use X=Z,Y=Z+t₁,s as parameters. Lifting that precise order gives x=αX+βY+δs² for δ a unit. Our residual equation XY=U x⁶ gives successively in the s direction after its two crossing blowups X₁Y₁=U s⁴(αX₁+βY₁+δs)⁶ and X₂Y₂=U s⁸(αX₂+βY₂+δ)⁶ (bracket unit at the origin). The other charts have linear exceptional equations. Four more ordinary point blowups resolve exponent eight, the last conic XY=ū s² smooth in characteristic two. These are the saturated regular ambient calculations of EVEN8 with the now checked exact hypothesis.

For c=0 one already has t₁=E'P(P+xγ/f). At its remaining origin blow up x=P=Z=0 (x,P cover) and normalize once more with an extra scale for Z. On x side P=xQ,Z=x²B gives B(B+E'Q(Q+γ/f))=U x². At the two simple roots Q=0,1 on the exceptional line the coefficient of B beside itself is a parameter together with x (f reduces to the constant f₀ along x=0 here, since f−f₀ divisible by t), so each is a smooth-conic ordinary node. One point blowup resolves each; outside the two roots the monic is étale. On the P chart x=PR,Z=P²B', one gets B'(B'+E'(1+Rγ/f))=U P²R⁶, étale over the R=0 side. Scale inversion, monic freeness and R₁/S₂ again prove the finite extra-scale charts are exactly normalizations. All remaining ordinary blowups use the nonzero divided equation on the ambient exceptional plane to prove saturation before regularity.

## Application at the two different types of third-stage points

For (j,k)=(1,2), h₀=8 and the E equation is already E(E+S)=(H₀/f⁸) w¹⁰. Keep only the V-equation in the base: it is regular at the w=S=0,V=1 point with parameters w,p=V−γ, since w is a nonzerodivisor and modulo w the S derivative there is V=1. Take r=M₀/f₀⁴. The exact base equation implies S=E'(V²−r) for a unit E': on moving all terms to one side, the terms other than V²−r are divisible by S and their quotient has residue 1 (the only linear term is SV, f−f₀=a₃d w⁶S², and (1+u)²−1=2w³S+w⁶S²). Thus x=w,t=S,f−f₀ divisible by t, and the preceding quadratic-contact terminal analysis applies with A=E and U=H₀/f⁸.

For j=0 and k=1 or 2, H/w⁶=H₀/f³, E=1. Put K=M₀/(ad H₀)=(e₀−e_m)/(e₀−e_k), Λ=2K−1. The equality b=w⁴V now gives V₀=y_m/w⁴=(2V+S)/(1+u), **rather than the unit-times-w coefficient of V in the A₀-odd case**. Then f V₀²=ad S²+4M₀/f³, so X=V₀/E, Y=S/E+2K satisfy Y²−(f/(ad))X²=4K(K−1). Here δ²=f₀/(ad) is available by an unramified coefficient comparison as f₀/(ad)≡1 mod4. Take ρ=1+2h' with ρ²=f/f₀ by a parameter-étale comparison. On both sides this gives the genuine common chart O[E'₀±] with its h' adjunction (do not confuse E'₀=ρ³ E with the generic unit E' above), π=w/ρ, π²=2f₀, S*=ρ³S, h'²+h'=a₃d π⁶ S*²/(4f₀), S*=(H₀/f₀³−E'₀²)/E'₀, as checked in PARITY16 in both directions. Now X'=δρX gives a **difference** of squares. The integral variable
    z=(Y−X')/2=K−δρ V/(E(1+u)) + [(1+u−δρ)/(2E(1+u))] S
has unit slope in V because δρ≡1 mod 2 as elements of the étale orders, and u=w³S is divisible by 2. Thus the true ring after these identifications is
    z(z−Y)=−K(K−1),   Y=Λ(1−Γ/E'₀²),    Γ=−H₀/(Λ f₀³).
This follows by the norm and unit-slope reverse substitutions, or by comparing the monic free quadratic algebras after inverting 2 and using scale torsion-freeness. At w=0,E'₀=1 the chosen original V=1 yields z=0, Y=0. Set x=π, A=z,t=−Y, p=E'₀−γ, r=Γ, E'=−Λ/E'₀². Then t=E'((γ+p)²−r) exactly and f=f₀ constant. The unit hypothesis −K(K−1)=Uπ¹⁰ follows from v₂(K−1)=5 for all four contact ratios. This is the same quadratic-contact terminal calculation under a genuine étale comparison, not division by 2 merely on the generic fibre.

For all 24 cases each step can use the reduced singular union, so the ordinary and normalized blowups commute with the acknowledged étale comparisons. The regular ambient saturated charts include non-rational directions. This gives a proper birational modification of the actual X_q on an open containing 2 and unchanged outside the closed origins (all the other mixed-parity points were already regular). Gluing to the prior D(2) model, as usual, gives the proper flat regular arithmetic model over Z for these 24 and unramified ratio variations. No unspecified coefficient family, semistability, minimality or Lean-checked result is implied.
