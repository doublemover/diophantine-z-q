# Any generic original scalar pair has a varying relative Kummer mark and a biquadratically split divisor

Fix ANY integer input a and ANY legal fixed integer label n≠0,1. On the literal two generic common scalar slots of forward-scalar-subsystem-sections-r1, a hypothetical PointPair cannot have the two original second Kummer slots in a constant ratio of squareclasses. Neither slot is assumed constant, and the two free twists may BOTH vary. Moreover some irreducible polynomial divisor of the common twist's odd support has at least four conjugate geometric components. These necessary conditions do NOT prove no generic pair exists, let alone no pair at an indexed rational specialization.

**Exact source notation.** Rename positive d=inputR(a) to avoid using the same letter for the input square root parameter. d>10, d≡5 mod17 for every integer a, A=114444d=102²·11d. F=Q(N,Q) is the field of the original two independent common slots (the second Q here is an indeterminate). Let W=N²+dQ², b=A(W/(1+A))², B=17b=βu² with β the positive squarefree representative, u a nonzero rational multiple of W. Write r=u/17, D=1−βr²=1−b/17, V=B²D. Thus [β]=[187d], v17(β)=1. These are precisely the source maps in the reviewed scalar-subsystem README e8692aac (source pointer below), before imposing the common integer multiple H. They do not change d when n changes.

A PointPair has parameter E, nonzero S, and abscissas B on E_E and BS² on E_EV, with E_g:y²=x(x−g)(x+3g). Write normalized gains e₁=E/B, e₂=EV/(BS²). Their ratio has squareclass D. After dividing ordinates by βu³ and β(uS)³, respectively, both satisfy

     Yᵢ²=β(1−eᵢ)(1+3eᵢ).

The earlier generic obstruction excludes y₁=0 or y₂=0 on F; one may use it here. In particular there are no zero factors in the following Kummer classes, and eᵢ≠0 since otherwise β is square. Let λ₁=[B−E], λ₂=[BS²−EV] be the SECOND slots of the two full split Kummer triples (root order 0,g,−3g). In normalized units λᵢ=[β(1−eᵢ)]. The first slot in BOTH triples is already β; their third slots are determined by the first two. Our stronger assertion is

     λ₁/λ₂ does not lie in Q× F×²/F×².

In particular it precludes a generic global realization of the successful local marking (β,1,β), even with both twists free. It does not preclude that marking on infinitely many rational specializations.

## An even-versus-odd degree calculation over a rational line

Let k be any characteristic-zero field with β and −3β both nonsquares, and r a transcendent. We claim one cannot have conic gains over k(r) as above with [e₁e₂]=[1−βr²] and λ₁=λ₂. We need only gains for which the ordinates are nonzero. For an individual gain use s=Y/(1−e). Then

    e=(s²−β)/(s²+3β),        [β(1−e)]=[s²+3β].

Use s,t for the two gains. Equality of their second classes gives a square
    y²=(s²+3β)(t²+3β)=(st+3β)²+3β(s−t)².
The identity
    (s²−β)(t²−β)=(st−β)²−β(s−t)²
shows that s=t would give [e₁e₂]=1, while st=β would give [e₁e₂]=[−β]. Both are impossible, since 1−βr² has simple zeros and is not a constant class. Thus v=(y−(st+3β))/(s−t) is nonzero and
    (3β−v²)(s−t)=2v(st+3β).
The exceptional vanishing of the coefficient 3β−v²+2vs in the resulting equation for t would force (3β−v²)s−6βv=0 too, hence s²=−3β, impossible. Therefore
    ρ=(s−t)/(st−β)=2v(s²+3β)/[(3β−v²)(s²−β)−8βvs]
and [1−βρ²]=[1−βr²]. In particular ρ is nonconstant.

First, deg ρ must be ODD. Over an algebraic closure, parity of the zeros and poles shows that among the two fibers of ρ above ±1/√β the only odd local degrees occur at r=±1/√β. A pole of ρ has even valuation contribution. Since an automorphism of the constants interchanges both conjugate points, the two odd local degrees belong to DISTINCT fibers. Each fiber degree is therefore odd.

Second, deg ρ must be EVEN. Regarding s=P/Q₀ and v=U/T as maps of the projective r-line with coprime pairs of binary forms of degrees i,j, the displayed fraction for ρ has homogeneous numerator/denominator of degree 2i+2j before cancellation:
    2UT(P²+3βQ₀²),
    (3βT²−U²)(P²−βQ₀²)−8βUT P Q₀.
At U=0 or T=0 a common zero must have (P/Q₀)²=β. Otherwise it must have (P/Q₀)²=−3β. The poles Q₀=0 introduce no further points: they would also require U or T zero and then the denominator cannot vanish. Thus every canceled closed point over k contains √β or √(−3β), and has EVEN residue degree. The entire common divisor has even degree with multiplicities, including at infinity. Conversely the original fraction is not identically constant or undefined. Hence its uncanceled map degree is even, a contradiction. This proof uses neither a rank heuristic nor Shioda–Tate, Faltings, or a choice of a rational section.

## Descent from literal source slots and the 17-adic last step

Suppose λ₁/λ₂=[c] for rational c≠0 over the original F. Set k₀=Q(√−d). In k₀ we have β nonsquare (positive nonsquare over Q and k₀ imaginary); also −3β nonsquare since [3β/d]=561 is nonsquare over Q. Set k=k₀(√c). The gain equations over F extend to k(r,X), since X=N+√−d Q and N−√−d Q=W/X is a rational function of r,X. The indeterminates r,X are algebraically independent. This really splits the original quadratic norm; it is not an assumption that d is −1. The two marks are equal after this constant extension. Specialize X to an element of the infinite constant field k avoiding the finitely many identically bad specializations over k(r). This retains both gain equations, their ratio 1−βr² up to a nonzero square, nonzero ordinates and equality of the marks. The preceding parity argument contradicts it if β and −3β remain nonsquares in k.

It follows that [c] is [β] or [−3β] over k₀: a constant nonsquare x can become square in a quadratic extension k₀(√c) only when [x]=[c]. The kernel on rational squareclasses from Q to k₀ is {1,−d}. Therefore over Q the only candidates for [c] are

    β,    −βd ≃ −187,    −3β,    3βd ≃ 561.

But c must be a norm from Q(√−3β). Indeed the same conic parametrization s,t, before extending constants, gives (st+3β)²+3β(s−t)²=c z² for some z≠0. Specialize the two independent N,Q to rational values avoiding all denominators and z=0. The binary norm is positive, so the two negative candidates fail. Locally at 17, the terms U² and 3βV² have unequal valuation parity, and a represented class of odd valuation therefore has [c/(3β)] square over Q₁₇: the second term dominates and the residual unit after division is 1 modulo 17. Both remaining candidates have odd valuation. For c=β the ratio class is 1/3, a nonsquare modulo 17; for c=3βd it is d≡5, again a nonsquare. Both are impossible. This completes the all-integer-input nonconstant-relative-mark theorem.

## A mandatory quartically split twist divisor

In the UFD Q[N,Q], a rational-function squareclass with even valuation at every irreducible polynomial differs from a constant by a square. Hence some irreducible f has odd v_f(λ₁/λ₂). It cannot be the divisor D=0: over Q(√β) that polynomial factors as two distinct conjugate curves W=±17/(c₀√β) where u=c₀W, each geometrically integral (the smooth projective conic N²+dQ²=nonzero). Thus D is irreducible over Q and the algebraic constant field in its residue field is Q(√β): it already contains √β via r, and the conic is geometrically integral there. The imaginary −3β stays nonsquare in that field. Each mark is a norm class from F(√−3β), as s²+3β or t²+3β. At the D valuation the nonsquare unit gives an unramified quadratic extension with residue degree two and forces even norm valuations. This excludes D.

At f≠D the gains e₁,e₂ have equal valuation parity, since e₂/e₁=B²D/S². The residue field is characteristic zero and β a unit. For a normalized equation Y²=β(1−e)(1+3e), its mark λ has odd valuation iff e has an odd-order POLE: for v(e)>0 both factors are units; if v(e)=0 and e reduces to 1, the factor 1+3e is a unit and forces even v(1−e); all other unit e give a unit mark. At a pole v(1−e)=v(e). Hence an odd relative valuation requires an odd pole on one gain and an odd ZERO on the other. On the zero side reducing Y² yields a square root of β in the residue field. On the pole side Y/e is a unit and reduces to a square root of −3β. Thus the function field of f contains Q(√β,√−3), degree four (β positive nonsquare). An irreducible plane curve in characteristic zero with this algebraic constant subfield splits over the algebraic closure into at least four conjugate geometric components, so its total polynomial degree is at least four. This follows also by tensoring the field with Qbar: the four embeddings separate into at least four factors. Since B=βu², E and EV are both odd at this f up to squares. The f is therefore a compulsory odd twist-support divisor on BOTH curves.

Consequently ansätze whose odd twist support consists only of absolutely irreducible curves, or only of polynomials of degree at most three, cannot work generically. Even allowing higher degrees is not sufficient: a qualifying divisor with the stated residue fields and opposite zero/pole behavior is necessary. No statement here prevents isolated rational pairs or positive-density/infinite rational specializations. The two common slots are generic, not a coherent actual evaluated h; this does not prove nonsolubility of a selected pole, nor of the four-source problem. No Lean execution.
