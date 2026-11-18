# All six mixed first-three odd sign patterns with fourth sign +1: terminal resolution

For each q⁰=(d₀,d₁,d₂,+1)∈{±1}⁴ with the first three signs mixed, and all twists whose four coefficient ratios with q⁰ are independently dyadically unramified, there is an explicitly chart-resolved, proper flat regular model over Z of the original parameter-preserving normalization. We continue the **actual** first mixed-origin blowup, add one normalized and one ordinary blowup, then reduce the last origin to a transverse split product of exact order ten. In four cases a local étale quadratic that genuinely splits a hidden discriminant is essential. This is not blanket descent through Q(i) at 2.

## One normalized and one ordinary blowup after the known first one

Use the majority indices j<k, minority m, repeated sign d and notation H=d(b_j−b_k)/4, M=d(b_m−b_j)/2, C=(343+b_j−1)/2, g=(1−d)/2 from RAMIFIED-DYADIC-FIRST12. Write H=2^h H₀, M=2⁴M₀, H₀,M₀ odd; h=3 for jk=01,02 and h=8 for jk=12. C+1 is divisible by 4 in all cases (j=0 or 1). At the unique successor of that first blowup, on its τ chart set u=τs, h_root=τA, l=τ(B_old), V=B_old−s. Its local equations are precisely
    τ²=2D,   D=C+τ+τs−τ²s−gτ²s²,
    A²+sA=H/τ²,   D V²+(2D+τ)sV+E s²=M/τ²,  E=D+τ+1.
The notation h_root distinguishes the actual majority half-root from the integer h. At this point D is a unit, (τ,s) are regular parameters of the two-dimensional base, and m=(τ,s,A,V). Every quotient of H or M by τ-powers below is interpreted as an actual integral expression using 2=τ²/D whenever the scale has not been inverted.

Blow up this reduced point. The τ,s directions cover: the two quadratic equations force leading A,V to vanish when both scales vanish. On the τ direction set s=τP,A=τa,V=τv. Here E=C+1+2τ+τ²P−τ³P−gτ⁴P² is divisible by τ². Adjoin b=v/τ to normalize; equivalently V=τ²b. The exact finite chart is
    a²+Pa=H/τ⁴,   D b²+L P b+J P²=M/τ⁶,
    L=1+τ,    J=E/τ²=(C+1)/(2D)+τ/D+P−τP−gτ²P² .
The extra b is integral by this monic equation up to the unit D. On τ=0 the residual relations are a(a+P)=0, b²+Pb+P³=0, since M/τ⁶ has valuation two in τ, C+1 divisible by 4, and D,L both reduce to 1. Where P≠0 both derivatives are units, so the hypersurface extensions are étale over the regular divisor there. At P=0 there remains a single F₂ origin a=b=0; both equations lie in the square of the ambient maximal ideal, hence the dimension-two local ring has edim four.

On the s direction τ=sR, A=s a, V=s² b (adjoin (V/s)/s). The equations are
    a²+a=H/(τ²s²),   D b²+(2D/s+R)b+E/s²=M/(τ²s⁴) .
All coefficients are integral by τ²=2D and this substitution: E=C+1+2sR+s²R−s³R²−g s⁴R², so E/s² reduces to R on s=0; the two constants reduce to zero. The exceptional equations a²+a=0, b²+Rb+R=0 are smooth at all primes: if R≠0 the b derivative is a unit; at R=b=0 the R derivative is 1. Thus the total space is regular there by the nonzerodivisor scale test. For both chart descriptions, start on the true blowup chart of the regular base surface at τ,s. The two new equations are separate monics in a,b (unit-leading for b), giving a free module over that base, scale a nonzerodivisor. Inverting the scale recovers the old localization with its exact field; hence the rings embed in that field. They contain the original ratio generators and are finite over the old ordinary ratio chart by the one new integral generator. They are S₂ by complete intersection and R₁ since off scale we started with a normal ring, and on scale all bad points just found are isolated in codimension two. Therefore they are precisely the finite normalizations of the ordinary charts, with matching ratio transitions in the common field. This stage is a **normalized** blowup; ordinary division by a second scale was not automatic.

Blow up the last reduced τ=P=a=b=0 point. The τ,P directions cover by its displayed quadratics and positive valuations of both right sides. On the P chart τ=PR,a=P A,b=P B:
    A²+A=H/(τ⁴P²),   D B²+L B+J=M/(τ⁶P²).
All coefficients are regular by h≥3 and v₂(M)=4. Both exceptional equations have unit derivative in their last variables (D,L reduce to 1), so the entire P side is regular. On the τ chart P=τS,a=τA,b=τB we obtain
    A²+SA=H/τ⁶,    D B²+L S B+J S²=M/τ⁸=M₀/D⁴ ,
    D=C+τ+τ³S−τ⁴S−gτ⁶S²,   J=(D+τ+1)/τ²,   L=1+τ .
Each ordinary chart has the indicated true ratios by independent monics over the regular base blowup and inversion of the nonzerodivisor scale. On the exceptional τ line both derivatives in A,B are units when S≠0; at S=0 one has B=1, A=1 for h=3 and A=0 for h=8. Only that one F₂ point remains. The argument below also gives edim three there and hence normality of this ordinary step by R₁/S₂. These formulas retain the full arithmetic coefficient action.

## Pair 12 (h=8): the small majority-root equation already splits transversely

Here H₀=−75d, M₀=−d. First keep just the B equation. Near τ=S=0,B=1 the base is regular two-dimensional with parameters τ,p=B−1: τ is a nonzerodivisor by monic freeness and modulo τ the single equation B²+SB=1 eliminates S with B a unit. In the regular three-dimensional ambient with the additional A put e=A,v=A+S. The surface equation is exactly
    ev=H₀ τ¹⁰/D⁸ .
The three functions e,v,p are regular parameters. Indeed the B relation mod the square gives S≡τ: D≡1+τ, B²≡1, J S² negligible, L≡1 mod the maximal ideal, and M₀/D⁴≡1 mod its square. Here 2∈(τ²). In the DVR ambient/(e,v) with parameter p one therefore has τ∈(p²), 2∈(p⁴). Setting S=0 in the actual relation gives
    (C+τ)⁵(1+p)²=M₀ .
Each odd constant is ≡1 mod p⁴ in this quotient; hence modulo p³ this reads 1+τ+p²=1. Thus τ has order exactly two in p. This is stronger than the linear tangent comparison.

## Pairs 01 and 02 (h=3): an exact étale discriminant and its genuine split product

Now H/τ⁶=G=H₀/D³. Over the regular base before either A or B is adjoined, invert L (a unit here). The crucial discriminant identity holds **on the chart**:
    L²−4DJ=(1+τ)²−4D(D+τ+1)/τ²=−1 ,
using τ²=2D. Adjoin θ satisfying θ²+θ=−DJ/L², and restrict to its étale neighbourhood above the dyadic point. In fact 1+2θ is a unit there, the equation is monic and the two special labels θ=0,1 are distinct since J≡0 at the origin. Thus this is a faithfully flat étale local comparison, unlike adjoining a generic ramified scalar without examining its integral ring. The unit i=L(1+2θ) satisfies i²=−1 and (L−i)/(2i)=−Lθ/i is **integral** on this chart. Set
    Y=(D/i)B+((L−i)/(2i))S .
This is an invertible integral linear coordinate change with unit coefficient of B. Direct expansion by L²−i²=4DJ gives
    Y²+SY=(D/i²)(D B²+L S B+J S²)=−M₀/D³=K G .
For jk=01, H₀=−d,M₀=2401d,K=2401; for jk=02, H₀=−2401d,M₀=d,K=1/2401. Both K and 2K−1 are units and v₂(K−1)=5 exactly. A=Y=1 in the selected residue.

First keep only A with A²+SA=G; the étale θ-extension is independent of Y and can be included in the base. At either θ label this is a regular two-dimensional base with parameters τ,p=A−1: τ nonzerodivisor and modulo it A²+SA=1 eliminates S; the finite étale base change preserves the parameter pair at the chosen fibre point. (In fact on the τ=0 divisor here J=0, so the two θ labels are étale-separated.) Invert A and use d'=Y/A−1, e=d'−(K−1), v=e+(2K−1)+G/A². Eliminating S and dividing by A² gives d'²+(1+G/A²)d'−(K−1)G/A²=0, equivalently the exact hypersurface
    ev=−K(K−1)=H₁ τ¹⁰,     H₁=−K((K−1)/32)/D⁵ a unit .
Conversely Y=A(1+e+K−1), so this is the actual ring presentation in a regular local three-dimensional ambient with variables τ,p,e. Since D≡1+τ, G≡1+τ, A⁻²≡1 mod the maximal square and 2∈(τ²), we have v≡e+τ mod that square. Thus e,v,p are regular parameters. In their ambient DVR quotient e=v=0, τ∈(p²), 2∈(p⁴) and
    D³ (1+p)²=−H₀/(2K−1) .
Modulo p³, D≡1+τ because its τ³S etc terms are negligible and C is odd; the odd rational right side is ≡1 mod p⁴. The equality therefore gives τ≡p² mod p³, i.e. precise order two. This calculation uses the correct unit K for each pair, not an identification of 2401 and its reciprocal.

## Termination on both sides of the case split

For all three majority pairs the actual (possibly chart-étale) residual hypersurface is e v=H τ¹⁰ in regular ambient parameters e,v,p, with H a unit and τ=αe+βv+γp² for γ a unit, by lifting the exact order in the DVR. The initial point is nonregular of edim three. Blow it up: the e,v directions have linear exceptional equations, and on the p chart E₁V₁=H p⁸(αE₁+βV₁+γp)¹⁰. Blow up the unique remaining crossing origin; in the p direction E₂V₂=H p¹⁶(αE₂+βV₂+γ)¹⁰ with final factor unit. Seven ordinary origin blowups take exponent sixteen down to two; the eighth at exponent two resolves the smooth exceptional conic XY=δZ², smooth even in characteristic two. At every step all divided equations have nonzero reduction on the regular ambient blowup chart, giving actual ratio subalgebras by cancellation; all noncontinuing directions are regular. These are exactly the intrinsic complete-transverse-form chart checks of TERMINAL-RESOLUTION §III, with the derived exponent, units and changed coordinates above. No regularity claim is inferred only from the generic equation.

The terminal loci over every preceding point are the reduced **whole** singular union, so the ordinary blowups and their regularity transport back along the étale θ comparison; its two labels are not a doubling of the number of geometric points on the downstairs scheme. The normalized second step is likewise intrinsic, finite normalization commuting with étale base change. Counting from the original mixed origin: first ordinary blowup, one normalized blowup, one ordinary blowup, two crossing blowups and eight transverse blowups, i.e. thirteen dyadic blowup rounds (one normalized). All later affected points are closed, and every stage is projective blowup or a finite normalization of it, proper and birational with the original field. For arbitrary unramified ratio twists the canonical reduced centers and this finite normalization descend through a genuine étale maximal-order coefficient cover near 2 as in SIGN-DESCENT. On a true open neighbourhood of 2 with all other modification and bad primes removed this modifies only the dyadic origins; glue to the previously reviewed arbitrary-twist D(2) model on the unchanged X_q. The resulting model of the actual projective normalization is proper flat regular over Z, not asserted minimal or semistable. Along with the prior two terminal fourth-negative types this settles eight of twelve mixed all-odd sign types by explicit full local constructions. No local Lean run, rank or final Diophantine implication.
