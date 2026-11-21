# One exact fixed-level coefficient tests rank-zero obstruction on the same receiver

Use the exact constant-conductor marked receiver
E′_d: y²=x(x−d)(x−81d) and its 2-isogenous
E_d: y²=x(x+16d)(x+25d), d=βθ>0 squarefree. The actual a=0
source has d≡17 mod24 and 5|d. Its required x-class θ is
neither 1 nor d and hence requires a nontorsion point.
We do not compute the following coefficient for the full
literal d. The result gives an exact, independently
falsifiable **obstruction criterion**, not a marked point.

## 1. The established formula really covers ramification at 5

The base conductor is 15, with Atkin–Lehner signs
ε(3)=+, ε(5)=−, ε(∞)=−. Its normalized newform is the
unique weight-two newform at level 15 (the modular curve
has genus one). Thus this is the very f used in
[Pacetti–Tornaría, §3](https://mate.dm.uba.ar/~apacetti/papers/Compositelevels.pdf),
despite using an isogenous elliptic model.

In [Sirolli–Tornaría, Theorem 9.2 and its construction](https://arxiv.org/pdf/2107.04483),
take F=Q, k=0, N=15 and type γ=(γ(3),γ(5),γ(∞))=(−,−,+).
The product with the Atkin–Lehner signs is +. At 3 one
must have (d/3)=−; at 5 one may have (d/5)=− **or 0** because
v₅(N)=1, 5 is odd, and γ(5)=ε(5). This latter alternative
is precisely the literal ramified-5 case, not an analytic
continuation from coprime twists. The auxiliary fundamental
discriminant is l=−23; its signs at 3 and 5 are + and − as
required by the order ramified at 3 and infinity.
L(f,−23,1) is strictly positive; the exact rational replay
below certifies this independently of the weighted formula.

The only type-II weight is at 3; the resulting level is
4·15·3=180. The modern theorem and its composite-level
discussion establish the older explicit examples, rather
than relying on a numeric table as proof of Waldspurger.
For the exact normalized form specified in the older §3.2,

    L(E_d,1) = 2^[5|d] k · c(d)^2 / sqrt(d),   k>0,

where c(d) is the coefficient of g_{−23}. In the literal
case the factor is 2, not 1. We use the classical centre
s=1 (the modern theorem uses a unitarily normalized centre
1/2). The older formula specifies k; its exact value is
irrelevant to the obstruction.

## 2. Explicit signed ternary lattice in integral coordinates

The ternary norm in that construction is
4x²+15y²+16z²−4xz. Write u=2x−z, so the lattice is
u,y,z integral with u≡z mod2, and the norm is

    Q(u,y,z)=u²+15(y²+z²).

For Q=23d, let b=10u+15y mod23 and define

    w_23(u,y,z) = (b/23) if b≠0, else (y/23),
    w_3(u,y,z)  = (u/3),

with zero Legendre symbol at residue zero. In the
[Mao–Rodriguez-Villegas–Tornaría weight convention](https://arxiv.org/pdf/math/0606762)
the first-kind weight can use the nonzero isotropic vector
(10,1,0) modulo 23, since 10²+15=115≡0. Its polar product
is 2b; 2 is square at 23. When b=0, two orthogonal isotropic
vectors for this unimodular rank-three form are collinear,
and the coordinate along (10,1,0) is y. This proves the
specified second branch, including the zero vector. The
type-II weight at 3 comes from the rank-one reduction u².
Changing the auxiliary isotropic vector or nonzero type-II
linear generator changes at most the common sign, and
the displayed choices give the published sign at c(5).

Pacetti–Tornaría take g_{−23}=2 times the generalized theta
series on this lattice with prefactor 1/4. Thus c(d) is
half the full lattice sum of w_23·w_3. In our type,
23d is 1 mod3, so u≠0 and −(u,y,z) has the same product
of odd weights. Consequently the exact integer is

    c(d) = SUM w_23(u,y,z) (u/3)
           over u>0, u≡z mod2, u²+15(y²+z²)=23d.

When 5|d, u=5U and the same signed sum instead imposes

    5U²+3(y²+z²)=23(d/5),  U>0, U≡z mod2,

with w_3=−(U/3) and first-kind b=4U+15y mod23. This is
exactly the same conductor-15 class, no replacement
squareclass or sum over a larger lattice. The finite
replay matches **all 15 signed** g_{−23} entries in the
published Table 4, with a second enumeration in the
ramified-5 normalization. For compact independent
numeric (not linked) profiles d=6953 and 13073 it gives
respectively c=0 and c=16, with 336 and 408 positive-u
lattice representations before weighting.

Independently for the auxiliary l=−23, the exact conductor
is 15·23² and sign is +. Splitting the Mellin integral
at the Fricke fixed centre gives
2 Σ a_n(n/23)e^{-2πn/sqrt(15·23²)}/n. The replay encloses
the exponential base between 931/1000 and 933/1000 by
alternating rational bounds, sums 300 signed terms with
exact rational intervals, and uses |a_n|/n≤n for the
geometric tail. This gives 31/50<L(f,−23,1)<89/125, hence
the nonzero auxiliary premise without circular reliance
on the displayed coefficient formula.

## 3. What could be concluded for the literal scalar

If one certifies c(βθ)≠0 for the actual sign-plus receiver,
then L(E_d,1)>0. The analytic-rank-zero
Gross–Zagier–Kolyvagin theorem gives rank zero for E_d and
for the 2-isogenous E′_d. Their rational torsion image
cannot contain θ, so the **constant-conductor receiver**
has no rational solution. This would not reject other
receiver families or the unrestricted original PointPair.
Conversely c(βθ)=0 gives no rational rank or marked point
without additional arithmetic; it is not a BSD input.

The exact y²=x(x−d)(x−81d) marking removes any appeal to
a two-derivative correlation across separate twists.
But evaluation of the full d or of this particular
coefficient at its enormous literal index is not supplied.
The finite algorithm and small controls are not a
compression of the actual source recurrence.

    python3 -B replay_weighted_ternary.py | cmp - EXACT-WALDSPURGER-CONTROLS.json
    sha256sum -c SHA256SUMS
