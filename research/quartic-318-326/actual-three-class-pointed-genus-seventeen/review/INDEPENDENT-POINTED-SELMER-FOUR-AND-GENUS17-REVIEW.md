# Independent review: pointed Selmer-four and a locally soluble genus-17 pullback

**Verdict: paper proof and exact local controls pass.** This binds author
note SHA-256 9d9bf8119c6ddc53f0fb112b0b8295ed50d64f7d215d09e1ca8ebc7c61f60447
and manifest SHA-256 4d43636fac9077b9097d249d88f680bc659854055ff1bc86ffd116f592c9545a.
Also checked the exact phase donor 9f08f6f2/534279af and the explicit
p47 local donor from ea83f1d1. Both donor scripts replayed byte-for-byte.

## Obstruction and governing primitive

For rational E[2], the obstruction to lifting the fixed F_* to
a global E[4] cocycle is a class in H²(Q,μ₂²). All ordinary local
Kummer lifts exist, so injectivity of localization (Kummer Hilbert 90
and Brauer–Hasse–Noether) kills that obstruction. At a selected strict
prime the exact correction subgroup is the kernel of H¹(E[2])→H¹(E[4]),
hence the connecting image κ₂(E[2](Q_p)); replacing it by the ordinary
Kummer subgroup would not remember the prescribed lift. The dual
condition is its local Weil annihilator, not the full local cohomology.
At ordinary places the correction group is the ordinary self-dual
Kummer image by the compatible maps to H¹(E). Subtracting a rational
torsion Kummer class at the varying prime is legitimate in this new
dual space. The normalized classes have fixed support and are locally
zero at either admissible varying prime.

I checked the obstruction quotient against [Milne, *Arithmetic
Duality Theorems*, I.4.10](https://www.jmilne.org/math/Books/ADTnot.pdf):
the product of correction subgroups is open in the restricted product
and self-unramified at almost all places. Its sum with the global
image is open and closed, so the dual test is both necessary and
sufficient for an actual global correction. No Sha finiteness or
local approximation theorem on the curves was used. At strict places
the marked F_* is itself κ₂(T_t), so it cups trivially with every
relaxed dual. Off them both are ordinary Kummer. Therefore Brauer
injectivity gives a global F₂ carry primitive; its restriction to
the common cocycle kernel is a central character. A rational
quadratic twist removes excess odd ramification outside the fixed set
as in [Smith, proof of Theorem 3.2](https://arxiv.org/pdf/1607.07860)
(the cocycle fields are unramified outside it and the ramified
relative places there form full rational orbits).

Independently compared two genuine global E[4] lifts β′,β after
the quadratic twist isomorphism φ. Their difference b=β′−φβ takes
values in E[2] and db=χ_d∪F_* in additive convention. Thus for a
relaxed tester F the discrepancy b∪F−χ_d∪Γ_F is a global 2-cocycle.
Its total invariant is zero. This recovers Smith's formula from the
proof, without claiming the published theorem already applies to
relaxed Selmer groups. At all fixed places the twists are locally
isomorphic and transport the chosen local κ₄(T_t) literally, so
local differences cancel. At odd good places outside the fixed set
and both varying primes, take unramified local lifts; the local
difference and correction are unramified. At either varying prime
the normalized tester is trivial, leaving exactly the unramified
governing character against the single odd valuation. The comparison
is the sum of the two Artin bits with no extra pointed local term.
On ordinary Sel₂ the obstruction is the original Cassels pairing,
so it kills rational torsion and the marked direction.

## Arithmetic and geometric seams

The two old central inertia pivots at p_a and 2399 still evaluate
to independent torsion points on F_*. The old annihilator proof
needs only the tests at infinity, 2, 3 and one odd collision where
the first coordinate has even valuation. The exact retained ordinary
prime 47 supplies the last: η≡1596 mod 47² and
407η²+32·2399≡1739=47·37 mod 47², with (−814/47)=+1. Thus the
proposed correction (−aδ,1,−aδ) has forbidden odd first valuation.
All the new governing fields have ramification supported on
the same fixed union, so the earlier finite Gaussian ray disjointness
and uniform gcd tails allow the chosen joint Frobenius. No
unchosen density theorem for auxiliary primes is introduced.

Adding κ₄(T_t) to the selected global normalized lift returns
to the raw mark and produces local 4-class zero at each strict prime
because κ₄(T_t) has order dividing two. The zero class gives a point
over O, where C₂ has its infinity fiber and the third equation has
a point since c is locally square. At 2 the prior test covers all
phases. At 3 the pinned inert product U mod 9 is (5,6), hence
η≡6 and c₂ is a unit. With the exact square-scaled cubic
(S₀,T₀/9,C/9,u)≡(2,2,1,2) mod 3 gives x=3 as a local point
in the missing odd-parity phase; its duplication has v₃(w²)≥2,
so w²−u is a square unit. T_t supplies the nontrivial unit phase.
At 47 the split nodal pair and nonsquare −1 give independent odd
valuation and unit torsion rows, so all phases are obtained by deck
translation. The four old support primes use the same deck argument;
the two third-factor support primes use both actual y-sign orbits
because their twist is nonsquare and the deck image alone has rank
one there. Only the squared parameter matters at these six places.

The C₄→C₂ covering is étale of degree 4. C₃→C₂ is a double cover
with eight distinct branch points (four over each simple root
±√u), so the pullback has 32 simple branch points over the genus-one
curve C₄; it is geometrically connected by the nonempty simple
branch divisor. Riemann–Hurwitz gives genus 17. At unlisted good
primes the same good integral fiber calculation and Hasse–Weil
give some local point, not automatically a specific old residue
ball. The same single pointed 4-cover works everywhere after choosing
q_c by the exact preceding third-factor selector.

No numeric clone primes, rational point, arbitrary old signed
residue-neighborhood approximation, global full detector, Sha
vanishing, or Lean result is claimed.

Signed: independent reviewer /root/high_review_ci.
