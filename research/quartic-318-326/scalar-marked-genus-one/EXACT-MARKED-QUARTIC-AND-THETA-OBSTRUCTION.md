# The literal marked two-twist search, with an exact scalar guard

Paper proof and source-map draft only. No claim of a new actual
complete_at_index witness, a chosen h, or a rank theorem. All
dependence on β, θ and the normalized physical pole is retained.

## Division-free marked producer and its converse

For β>0 and integer A,B with AB≠0, set
    R = βA²+3B²      U = 2(3B²−βA²)      V = 4βAB
    M = β(βA²−B²)(βA²−9B²).
At X=βR² and Y=βRUV one has by expansion
(X-M=V^2) and (X+3M=βU^2).
Thus (Y^2=X(X-M)(X+3M)), with the ordered mark (β,1).
If M>0 then R,U,V are all nonzero (U=0 would force M<0).
Whenever (M=nW^2), W≠0, divide R,U,V by W,
X by W² and Y by W³. This gives literal
ActualTwoDescentPointExtraction318.KummerPoint β n.

Conversely take that actual Kummer point with n>0 and β>0.
Its x is βr² for a nonzero r by KummerPoint.squareclass. Then
((2r-u)(2r+u)=3v²/β), so t=(2r−u)/v≠0 exists.
Solving gives (r/v=(βt^2+3)/(4βt)) and
(n/v²=(βt²-1)(βt²-9)/(16βt²)).
Writing t=A/B in reduced terms recovers the above formula
with (W=4βAB/v). This is therefore an exact marked
genus-one search on the same curve, not a test based on
unmarked positive rank.

One pair of such representations with M=nW² and
M'=nθW'² (same n, β, θ from the actual b) gives the two
inputs of actual_realization_of_kummer and hence PointPair b.
For θ=1 the same representation suffices. Otherwise one
marked side alone does not give the other.

## Original selectability, including the special primes

If using the **original chosen selector**, not merely seeking a
PointPair by any means, write q_B=supp β, J=supp θ, d=|q_B|.
By V13 original-seven-simultaneous-realization, lines 7788–7833:
require positive squarefree n, coprime to 6θ, n≡11 mod12, and
precisely d additional prime slots: one q₀ type (s,λ)=(1,1)
and d−1 I type (0,0). At q_B the prescribed columns for I
are e_i+e_d in whatever original ordered indexing is used.
All other I incident entries are zero; q₀--q_B entries are
the row sums; reverse directions use reciprocity. At J the
q₀ bits are the actual ones, and the enlarged K-sharp deleted
determinant must be nonzero. Concrete candidates from the
quartic must pass these tests on their genuine supports,
not simply be accepted because β divides n.

For a primitive A,B with gcd(B,β)=1, put F1=βA²−B² and
F9=βA²−9B². A prime p≥5 divides at most one of F1,F9 and no
p|β is in either. A prime from either factor sees β as a
unit square; the entire F1F9 is a square at every q|β
because F1F9≡9B⁴ (mod q). Both statements persist after
squarefree extraction on n/β. This gives the correct
whole-product symbol conditions, but not the individual
columns or q₀ types. In the full candidate, a p|θ occupies
an actual positive valuation in one of F1,F9 because p≥5,
and is distinct from all q_B and from the small-side n.

At p=3 use β≡2 mod3. For primitive A,B, the 3-adic
valuation of the factor product is always even:
* If 3|B, both factors are units ≡2 mod3.
* If 3∤AB, their residues are 1,2.
* If A=3C and 3∤B, the first is 2 and the second is
  9(βC²−B²), with residual unit 1 if 3∤C, 2 otherwise.
Including the prefactor β, squarefree n reduces to 2 mod3
exactly when 3|B or 9|A.

At p=2 choose √β in Q₂, as β≡1 mod8, and let w=√β A/B.
If v₂(w)<0, remove w⁴: both residual units
1−w⁻², 1−9w⁻² are equal modulo 8. If v₂(w)>0,
w²−1 and w²−9 are equal odd units modulo 8. In either
case their product and n are Q₂-squares, impossible for
n≡11 mod12, n odd and hence n≡3 mod4. Thus v₂(w)=0,
so A,B are both odd in reduced terms. The two original
factors have valuations ≥3; since their difference is 8B²,
one has exact valuation 3 and the other higher. Odd n
requires that the second valuation also be odd. These are
necessary, then the odd residual unit of n must separately
be checked to have residue 3 mod4.

## θ on the actual scalar datum, and a useful no-go

For the selected actual scalar A_s=114444R write
(A_s=17^2 K u_0^2) with K positive squarefree. For its
same chart ratio W_s=m/d₀>0, put Z=(1+A_s)d₀,
C=u₀m and β=17K. Precisely
    b = 17² K C²/Z²
    1−b/17 = (Z²−βC²)/Z²
    θ = sf(Z²−βC²).
The numerator is positive by b<17. Taking its squarefree
part makes no assumption on the magnitude of the exact
chart denominator. This is the actual finite integer to
factor at each fixed h. Equivalently (z=C/Z) realizes
(1-βz²=θ e²) with the *same* θ. The already checked
Ready→Eligibility gives θ≡1 mod24 and all the mutual
product conditions, not θ=1.

The tempting targeted choice t=z or t=3z uses the
theta relation to insert θ into one entire quartic
factor. It cannot give an odd selected full nθ≡11 mod12,
regardless of the chosen θ-norm representation. In fact
**neither signed factor can have squareclass θ or −θ**
for such a selected representation: by the previous
2-adic argument both factors have odd v₂, whereas θ is a
unit square in Q₂ and ±θ has even v₂. This is not a
general failure of the quartic generator. An actual
target must share its two odd 2-adic powers, possibly
also splitting θ across both raw factors, and satisfy
the remaining β-local symbols before factoring.

For example t=z does give a concrete *one-sided* marked
curve with full parameter of class βθ(9−βz²), but it is
not the chosen original residue-11 curve. Prescribing
class 2θ for its whole one factor instead is not a universal
fix either: if a q|β has (±2/q)=−1 for the chosen sign,
the norm equation for that class fails mod q, since θ
is a local square there. In the actual a=0 scalar β,
q=5 rules out both signs because (±2/5)=−1.
A further odd multiplier or a split θ support is needed.

## Exact boundary of the standard simultaneous-twist family

[Kuwata, Proposition 2.1 and Corollary 2.3](https://tiger.math.okayama-u.ac.jp/mjou/mjou47/_08_Kuwata.pdf#page=3)
supply positive rank on simultaneous twists of an elliptic curve with
a rational nonzero 2-torsion point. They do not impose the mark or selector.
In fact their displayed rational construction can be checked more precisely
on this exact family before trying a search.

For normalized F(x)=x(x−1)(x+3), write k=θt²>0. At source root 0
the two x-parameters are v=3(1+k)/2 and v/k.
Directly F(v/k)=F(v)/k³, so with d=F(v)>0 the two
homogeneous coordinates are (dv,d²) on E_d and
(dv/t²,d²/t³) on E_(dθ). Their homogeneous x-class is
the SAME, namely class (3/4)(1+3k)(3+k).

That class is never the actual β≡17 mod24. At 3, θ is a
unit square. For v₃(t)=0, the class has odd valuation 1.
For v₃(t)>0 it has valuation 2 with square residual unit,
whereas β has nonsquare unit residue 2. For v₃(t)<0 use
the exact invariance of the class under k↔1/k. Thus the
standard pair at the distinguished root 0 fails the required
mark even before imposing the detailed original selector.

One cannot repair this particular construction by translating to
the other rational roots. Using the same formula based at root
q with A_q=3q+2, B_q=F′(q), the two original normalized
coordinates are q−(B_q/A_q)(1+k) and
q−(B_q/A_q)(1+1/k). For q=1, their simultaneous positivity
would require both k<1/4 and k>4. For q=−3, positivity forces
3/4<k<4/3, where both coordinates are strictly below 1,
so F is negative and gives the wrong sign of d. This diagnoses
only these particular parameter families, not every possible
simultaneous-twist construction.

The remaining constructive task, once one actual h and θ are explicit,
is a pair of rational quartic points matching the same n and nθ
with the exact β mark. No proof of that producer is asserted here.
