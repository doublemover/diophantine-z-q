# Exact next-cover τ cosets and what the aggregate L test decides

Use the same h,J,c=C/Z, β, H=Z²−βC², L=25βC²−9Z² and
two surviving ξ values from the independently reviewed next cover.
This is an arithmetic necessary-condition computation, not a proof
of local or global solubility for either ξ. In what follows
τ means the positive reduced squarefree representative of τ_int.

## The exact denominator residue at 2 and a fixed character product

The four prime factors of 1+A are all 5 mod 8. W is a unit at
181,1346909,70850399941: the compact lift computes the nonzero
residues 146,429536,66349154550. For p=29 both integral local
elliptic charts have residue zero, as the targeted exact computation
shows. Since i=mh, their formal doubled-abscissa parameters give the
ratio U(i)/U(h) nonnegative valuation; hence Q is integral and
N≡1. As −R_input is nonsquare modulo 29, W is again a unit.
So all four factors enter the reduced denominator Z exactly once.

All other odd primes entering Z to odd valuation split 2,−1,
7 and −R_input, by the independently reviewed crossed-pole
reduction. In particular they are 1 mod 8. Therefore Z≡1 mod8.
At the four fixed denominator factors the characters of −R_input
are (−,+,+,−); those of 7 are (+,−,+,−). It follows that
    (−R_input/Z)=(R_input/Z)=(7/Z)=+1.
In particular the product of (Z/p) over the odd prime support of
R_input, namely 5,163,661,733,1489,1861, is +1. These statements
do not determine (η/Z) for η=−2·1861·2027·83761.

## Fixed local cosets for the actual next cover

At infinity τ_norm and τ_int are positive. At ξ₂>0 use the previously
verified sample (a,d)=(0,1); at ξ₁<0 use (a,d)=(1,0) and U<0.
Then t_G<0 since a₀²=βd₀²+|ξ₁|V₀², and t_F<0 termwise.

At 2 the E x-class subgroup is trivial. In the model
y²=x[(x-K)²+M²x], K=9βδ≡1 mod8 and v₂(M)=5.
For nonunit x the norm correction to the leading square has
depth at least 3, so x must itself be square. For an odd
nonsquare x, v₂(x−K)≤2, hence again the correction
M²x/(x−K)² has depth at least 6 and x cannot work.
For ξ₂ the normalized tangent ratio is unit 7 mod8 by the
checked aggregate receipt. For ξ₁ choose d=1 and G=56,
thus a²=β−56. The exact c≡76 mod256 follows from v₂(m)=16,
v₂(Q)=2, v₂(N−1)≥9 and hence W≡1 mod64. Choose
    a≡209 (mod256), V/2≡23 (mod64), U/V≡9 (mod64).
The squares lift (the adjacent checker validates the necessary
extra digit precision); the normalized tangent numerator and
denominator are 254 and146 mod256, both valuation one and giving
ratio unit7 mod8. Thus both τInt have exact local class 7.

At 3 the rescaling by x=9x', y=27y' gives good reduction
y'²=x'(x'²+1): the local x-class subgroup consists of both
unit classes. For ξ₂ use the corrected a=−1,d=1,V≡−1,
U/3≡1. For ξ₁ use a=0,d=1,V≡1,U/3≡1. In the latter
case ξ₁≡2, seed a₀,d₀,V₀≡0,2,1 and c/3≡1.
Both F/9 and G have the required unit nonsquare residue for
the ξ₁ roots. Then t_G≡1−2≠0 and t_F/3≡1−2≠0.
In both cases the valuation of the tangent quotient is odd.
Since Z is unit at 3, v₃τ=1 in the squarefree representative.

For every p|β the E x-class subgroup is {1,β}: if x is a
unit or has valuation ≤0 or ≥2, comparing
(x−K)² to M²x forces x itself to be a square unit class
after its even valuations are removed. If v_p(x)=1 then a point
must have x≡K mod p² (otherwise the polynomial has odd valuation);
here x has class β. The order-four point attains it.
Our normalized tangent ratio has class 1/3 at every such p,
regardless of whether ξ is unramified or ramified:
* If ξ is a unit of class −1, use (a,d)=(1,0).
  The primitive seed a₀,V₀ are units; otherwise
  β d₀²=a₀²+ξV₀² would force all three entries divisible by p.
  Choose the two root signs to give t_G≡−2a₀ and
  t_F≡−6a₀, so the normalized ratio is 1/3 mod p.
* If ξ has local class β, use (a,d)=(0,1). Now a₀ is
  divisible by p and d₀,V₀ are units by primitiveness.
  Choose V and U≡3V modp so that t_G/p≡2(β/p)d₀
  and t_F/p≡6(β/p)d₀ (β/p is the integer quotient).
  Again the normalized ratio is 1/3 mod p.

Thus the exact odd β condition is
    τ Z / 3 ∈ {1,β} in Q_p×/Q_p×².
The existing exact rows at 2027 and 83761 show that τ
has valuation one at its activated L prime P and zero
at the other. In particular any global lift in these fields
has a next class of the shape
    τ=3 P B_* H_* >0,   τ≡7 mod8,
where B_* is a squarefree divisor of β and H_* a squarefree
divisor of rad(H) (possibly involving unseen primes).
The independent support proof excludes all other prime factors.

## Actual L aggregate and its exact redundancy

At any odd p|L outside the activated prime of ξ, ξ is unit.
Choose the square root ρ of β locally with 3Zρ≡5βC modp.
Writing x=a/ρ, the split coordinates of G/β are
ℓ=d−x and r=d+x. The second split coordinate
r_F of F/β under the normalized linear map is
    r_F ≡ −(12/5) ℓ (mod p).
On the split conic in either pair of coordinates the tangent
class with seed (ℓ₀,r₀,V₀) can be evaluated exactly as
    t = ξ(ℓ₀ V−ℓ V₀)²/(2ℓ₀ℓ),
and also with r in place of ℓ. Choose a local point with
ℓ and r_F units (the two-character proof permits this);
choose root signs to avoid zero tangents. Thus
t_F/t_G has class (−5/12)(ℓ₀/r₀), and
ℓ₀/r₀ has class ξ since β is split. As 9δ is a square
unit when p|L, the normalized tangent class is −15ξ.
When v_p(L) is odd this coset is exact, because E's
local x-class subgroup at that L prime is trivial.
At the activated prime P the actual earlier ramified local
row gives the exceptional sign κ:
    χ_P((τ_norm/P)/(−15·(ξ/P))) = κ,
where κ=+1 for ξ₁,P=83761 and κ=−1 for ξ₂,P=2027.

Let g=sf(−15τ/ξ), coprime to L (activated valuations cancel,
and 3 in L occurs to order 2). All other L primes are odd
p≥11 outside β and H. Multiplying the odd-valuation L rows
gives the exact aggregate
    (gZ/|L|)=κ.
Since |L|≡1 mod8 and Z≡1 mod8, reciprocity converts its factors:
at p|β the residue of |L| is 9Z², a square; at p|H it is
−16Z². Also (Z/|L|)=(|L|/Z)=(β/Z) by coprimality
and L≡25βC² mod Z. Thus the L aggregate becomes
    (−1/H_*) · (β/Z) = κ.

The product of the β local constraints already gives
    (β/Z)=(−1/B_*).
Indeed the factors from P and H_* are square when the
β character is evaluated at their primes, so reciprocity
eliminates them. The remaining cross-product over
p|B_*, q|β/B_* pairs (p/q)(q/p); β≡1 mod4 means
the total number of 3 mod4 factors of β is even, and
the cross-product is exactly (−1/B_*).
Consequently (−1/(B_* H_*))=κ, which is already
forced by τ≡7 mod8, because τ=3P B_*H_* and
(−1/(3P)) is −1 for P=83761, +1 for P=2027.
This aggregate L calculation is useful for avoiding a
false further Cassels obstruction; it provides no new elimination.

The compact checker enumerates candidate τ on the **specified**
known support, passing the 2-class and the exact product
character at the fixed R primes. If no H primes are admitted,
32 candidates remain for each ξ. Admitting the four already
known H primes gives 512 each. The fixed-place unit labels
at β and L would require the actual unit characters of Z;
the displayed candidates are not asserted to be locally
valid τ choices. Unseen H factors remain possible.
