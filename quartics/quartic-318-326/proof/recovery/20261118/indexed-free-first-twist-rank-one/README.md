# On the actual two free twists: exact first rank, odd analytic signs and a single baseline partner class

At the explicit integer input a=0 or −1 and actual common index h=328655617654071015360, keep the same indexed b and true complement θ, *not* a model replacement. The free parameter t=18 below gives the following results on the two ORIGINAL curves y²=x(x−E)(x+3E) and y²=x(x−EV)(x+3EV), not on the auxiliary matching Jacobians:

* The first curve has rational rank exactly one and Sha[2∞]=0. Its displayed non-torsion marked point represents the unique free rank-one bit modulo doubling and torsion; no primitive integral Mordell–Weil generator claim.
* Both original curves have analytic root sign −, hence odd analytic rank at least one. Exact analytic rank, or positivity of the second rational rank, is not deduced from parity.
* On the second curve the specific first-abscissa full class (β,1,β) is everywhere locally soluble and not a torsion Kummer image. It is the ONLY nonidentity class in the part of the full 2-Selmer group supported on −1,2,3 and the primes of the first squarefree twist. A rational lift would give the nonzero second ordinate of the literal PointPair at the same b, but the existence of that lift, the whole second Selmer group and any rank/Sha bound depending on its omitted primes remain open.

## Uniform sign and marking on every source-prepared pole

Write B=17b=βu², D=1−b/17=θz², V=B²D, where β,θ are positive squarefree, u,z rational nonzero. Use 0<b<17, square reduced denominator, v₂(b)≥3, v₃(b)≥1, v₁₇(b) even ≥2, and for the SIGN assertion specifically assume b is square in Q₂ and Q₃. These last local square conditions are real conditions, not consequences of the numerical depths alone. They are part of actual scalar SmallPrepared, imported into AllScalarSupportPreparation318.Prepared; the true contact ray row product consists of primes 1 mod408 times a square, giving them as well when its original preparation is supplied. Positivity without full preparation is not enough.

Then β≡17 mod24: b has unit squareclass 1 in Q₂,Q₃, and 17b has classes 1 in Q₂, 2 in Q₃. Since D is a local square at 2,3 by depth, θ≡1 mod24. For ANY nonzero integer t divisible by 6 set

    e=(1−βt²)(1−9βt²)/(1+3βt²)²,  E=Be.

As β≥17, e>0. It is a local square at 2 and 3, so the positive squarefree amplitudes of E and EV both have residue 17 mod24. On E_a:y²=x(x−a)(x+3a), E₁ has conductor 24 and global sign + (local factors −,+ at 2,3 and − at infinity). For positive squarefree a≡17 mod24, discriminant a is coprime to 24 and the quadratic twist formula gives w(E_a)=χ_a(−24)w(E₁)=−1. Equivalently (2/a)=1 and (3/a)=−1. See [Dujella et al., On the high rank π/3 and 2π/3-congruent number elliptic curves](https://arxiv.org/abs/1102.4291), the 24-conductor positive-sign base family. By modularity its associated L-functions have the functional equation, so the asserted analytic zeros are unconditional. No analytic leading derivative is computed.

In the earlier coherent construction t was taken divisible by 6βθ; divisibility by βθ is NOT necessary here. At p|β, θ is a local square by the prepared denominator and depths, and e≡1 mod p for odd p regardless of t. At 2,3 the two parameters are square in the necessary classes. At other p|θ, β is a local square, so the triple δ=(β,1,β) is trivial. A new p∤6βθ with odd valuation of e divides 1−βt² or 1−9βt² and hence β is a local square. At all other odd good primes every unit triple with square product is in the full Kummer image. As in forward-prescribed-pole-coherent-selmer-r1 this puts δ in Sel₂ of the same true partner E_EV, with the first marked point already rational. Thus t=6 is an unconditional uniformly small choice for both analytic signs plus one global non-torsion point and this coherent partner class. Fresh-prime constructions give infinitely many distinct twist classes with these two signs if desired. This does not by itself make δ globally rational, nor assert an exact uniform rank-one theorem for all β.

## Exact t=18 result on the indexed first twist

For the indexed witness β=204618888056724185. Here F=(1−βt²)(1−9βt²) and n=βF is positive squarefree:

    n = 8094120968054829661910126903116889587959583856144085429185.

The complete baseline prime support beyond the eight known β primes is 7,109,131,3108863,729975509,833212819,209296670729. The true first E has E/n=(u/(1+3βt²))². In the integer n-model the original first-abscissa point is

    X=β(1+3βt²)², Y=8β²t(1+3βt²)(1−3βt²);
    X−n=(4βt)², X+3n=β·(2(1−3βt²))².

These identities give its full triple. On E_n rational 4-torsion is impossible already locally at 17: each nonzero rational root has a difference of odd 17-adic valuation, preventing halving in the split Kummer test. The rational torsion Kummer images thus come from E_n[2], since odd torsion is divisible by 2. At the roots n,−3n the abscissa has odd valuation at the fresh prime 131 whereas β is a unit; the O and 0 classes have first coordinate 1 or −3. None equals β. Hence the first point is non-torsion.

In root order 0,n,−3n the complete first split Sel₂ has dimension three, with ordered-pair basis

    (−3,−n),  (β,1),  (n/β,1).

The exact calculation includes all bad places infinity and the prime divisors of 6n. At all good odd primes each entry must have even valuation, and conversely every unit pair is a local image by good reduction, so the finite signed support suffices. Locally at the tested p the explicit root images and true non-root abscissas are accepted only when all three factors have square product in Qp. Finding 4 distinct images at odd p, 8 at 2 exhausts the local group modulo 2 (formal group index). At the real place the two sign bits coincide. Intersecting these exact local images over F₂ gives the displayed basis. This bounds rank by 3−2=1, attained by the actual marked point. Thus all of Sel₂ is rational and Sha[2]=0, which implies Sha[2∞]=0 without assuming finiteness of all Sha.

## The actual OTHER free curve, not a guessed squarefree complement

The true second parameter EV is rational-square equivalent to nθ. The same finite local arithmetic, now restricting the two global entries to the signed group G generated by 2,3 and all primes dividing n, leaves only the nonidentity pair (β,1). For the local target twist at the β primes and 2,3 use [θ]=1 from actual preparation, not an independent sample. The original orbit calculation for all remaining needed p tests θ through D. Prime 7 uses the two split components (one smooth additive cusp, the other good formal) to give D=6 mod7 as in forward-indexed-matching-root-signs-r1. At 61,109,6551,17377 use the true D modulo p²; 109 divides both n and θ so it cancels from the squarefree amplitude of nθ. All other needed residues are certified from the original division polynomials and exact multipliers. At infinity keep the same sign condition. These local tests alone give the upper bound, so the unknown support of θ need not be factored. The already proved local existence of δ at ALL places gives the exact lower bound. We conclude Sel₂(E_(nθ))∩G²={0,δ}, not that the *complete* Sel₂ has dimension one. In fact rational 2-torsion also contributes to the full group. At 61 outside G, nθ and all root differences have odd valuation, so no local 4-torsion, and the three nonidentity roots have nonzero valuation signatures. Hence global δ, whose entries are units there, is not a torsion class. Any rational lift is non-torsion with the required abscissa squareclass; conversely a non-lift would give a specific obstruction in Sha[2]. Ruling out this full triple need not rule out another permissible marking or parameter.

Run python3 -B verify.py and compare REPLAY.json. Arithmetic includes a complete recursive Lucas primality certificate for every factor, the exact first point, both Kummer eliminations, and the original source orbits with verified annihilators rather than assumed CM orders. No external package is required. Input constants/source bindings are in forward-actual-local-index-constructor-r1 (db5260f384db48f1cc58f96a88ea97de1f6c388697d0b9e3546bb15886fe8c9f), forward-indexed-complement-selmer-ramification-r1 (8028efec8d9f6f05c4930130981daba876152ebd18296cb7c3b6b1f9a329e734), and NormalizedPolePoints318.lean at a0950ac7c24df6d336a196966fb790d6abd55e44. This is a source/math result, not a Lean elaboration or a solution of the four missing square equations.
