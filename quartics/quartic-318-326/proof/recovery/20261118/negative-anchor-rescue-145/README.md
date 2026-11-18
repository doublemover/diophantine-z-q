# Positive anchor fails, negative anchor works, at the same doubly nonsquare pole

This example separates the two one-torsion strategies. For the same
prepared b we prove the positive canonical quartic has no rational
point, produce an explicit negative-anchor solution with precisely the
first ordinate zero, and independently give another solution with both
ordinates nonzero. Both the first class and the complementary class are
nonsquares. This differs from the b=(204/1073)² example, where *both*
signs are obstructed. These examples cannot be merged into one
assignment; neither is a claim about the four selected input poles.

Take m=145=5·29, β=17m=2465, θ=2449=31·79 and N=βθ=6036785. Then

    β·12²+θ·47²=2401²,
    b=m(204/2401)²=6034320/5764801,
    D=1−b/17=θ(47/2401)².

Thus 0<b<17, b has exact depths (4,2,2) at 2,3,17 and square reduced
denominator. The unit class m is square at all three (1 mod8, 1 mod3,
9 mod17). Put B=17b, V=B²D, F_n(x)=x(x−n)(x+3n).

## Positive anchor: an explicit nontrivial Cassels row

A point on W²=θ(s²−βt²)(s²+3βt²) would yield x=θ(s/t)² on
E_N:y²=F_N(x), hence first descent class θ. Here t=0 requires θ
square, s=0 gives a negative radicand, and W=0 is excluded by β>0
nonsquare. In the full descent with root order (0,N,−3N), take the
usual classes ([x],[x−N]) and torsion conventions. The first-θ Selmer
fiber contains only α=(2449,1), unlike the two lifts at the earlier
409 example. Companion ε=(−17,−290) is in Sel₂.

In detail, at the real place,2 and each odd bad prime 3,5,17,29,31,79,
we generate local Kummer images with genuine local points, by checking
the cubic at rational x and evaluating all three torsion roots. The
generated subgroups attain the full local cardinalities 2,8,4,…,4.
At other primes all Selmer coordinates have even valuations by good
reduction and separation of the three roots; the four unit pairs are
the full image by the same cardinality bound. The global search over
all 256 signed squarefree second coordinates contains exactly one lift
above 2449. The local image procedure is the unchanged standalone
implementation from the preceding exact positive-anchor packet.

Use the pinned general norm-prepared Cassels row in PAIRING.md
(SHA256 f4ca4fddc6afecd93539e71698908a840b9ea1d5ae412ae70160b30b035a7849),
with primitive norm data A=12, E=47, denominator 2401. In the dyadic
factor ℓ=2·2401·5. For ε=(x,y), the 2-factor is (ℓ,x)₂(−ℓ,xy)₂,
the 3-factor (−1)^v₃(x), and infinity contributes +1. At p|β the
factor is (−1/p)^v_p(x)·(−2·2401/p)^v_p(y); at p|θ it is
(−2/p)^v_p(x)·(−3·2401/p)^v_p(y), where the odd symbols are Legendre
symbols. The general normalized tangent argument gives +1 at each
remaining prime (primitive contacts with even evaluations). At
x=−17, y=−290, the negative local factors are exactly **2,5,29**;
the other factors are +1. Thus the product is −1. Rational Kummer
classes are in the radical of the Cassels pairing, so the sole lift
α is not represented. This excludes the full positive canonical
quartic, not just one tried affine parameter. The tangent convention
is [Shukla, §3.1.1 and Theorem 3.3.7](https://epub.uni-bayreuth.de/id/eprint/8348/1/thesis.pdf).
No analytic rank, PARI rank, or finiteness of Sha is used.

## The other sign actually works

On E_(−3N):Y²=X(X+3N)(X−9N), the following is an actual rational point:

    X=668907746699090752665/40276074721=β(520924341/200689)²,
    Y=17281222670980383356489001364800/8082965159682769.

No group generator or numerical search bound is needed; substitute
directly. Put u=204/2401, v=B·47/2401 and r=520924341/200689, so
B=βu² and V=θv². Choose E=−B/3, S=vr/3. Since
EV=−3N(uv/3)² and BS²=X(uv/3)², take y₁=0,
y₂=Y(uv/3)³≠0. This is a literal PointPair on the same b.
The positive E=B alternative is excluded: its rescaled second point
on E_N would have x-class β, and translation by (N,0) changes this to
class θ. Indeed a zero second ordinate is equivalent, by the exact
pair swap, to one of the corresponding first-ordinate strategies.

## Both ordinates can be nonzero at exactly this same b

Apply forward-two-seed-prescribed-pair-r1 with λ=12, μ=175 and this
β. Put s=(λ²−3β)/(2λ), J=(λ²+3β)/(2λ), and t,K analogously at μ.
The joined seed has h=(s−t)/(st−β)=489/29881, b₀=m(17h)². The
transport multipliers X=119524/391363 and Z=1404407/845152 satisfy
b=b₀X² and D=(1−b₀/17)Z². The standalone checker reconstructs and
checks both nonzero ordinates from exact rational formulas, in addition
to the separate first-ordinate-zero witness above. Hence both strategies
succeed on the *same* global classes and pole, but on different first
twists, as required. By the separately reviewed torsion transfer on
these prepared abscissas, every ordinate asserted nonzero gives a point
of infinite order on its own twist. This is not a computation of all
rank or Sha groups of this example.

Run python3 -B verify.py; compare output to FINITE-REPLAY.json.
