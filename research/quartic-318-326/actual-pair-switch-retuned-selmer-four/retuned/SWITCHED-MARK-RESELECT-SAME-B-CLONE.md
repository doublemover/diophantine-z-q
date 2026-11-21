# Preserve the actual pair-switch balance and retune the full marked Sel₄ lift

Fix the switched two-class construction of 7cc3bf7b…, its actual
XVI constants (same J,s,t), and write its provisional b-clone as
q_b*. Keep a, the selected new pair d=r₁r₂, and their local w² balls.
The old normalization is always at the **b-clone**, never at r₂.
In this setup there is an order-compatible replacement q_b of q_b*
preserving the entire fixed normalized switched Sel₂ space and
both dimension drops; for this replacement the literal switched
mark is in the image of the full Sel₄. This only concerns the
two-class genus-one cover. The proof retains the original XVI and
fixed pair balls and supplies a new q_b ball in place of q_b*.
It supplies no hyperbolic complementary block, rank, global
rational point, or numerical choice of primes.

## 1. Use q_b* as a new finite reference, not as a retained contact

Before choosing r₁,r₂ in the pair-switch producer, additionally
exclude the finitely many primes dividing N((π_b*)⁴−1), where
π_b* is the Gaussian generator of q_b*. This guarantees the actual
generator avoids μ₄ in both components at both primes of the pair.
Choice from a positive-density set is unchanged by these finitely
many exclusions. In the r₁,r₂ order selections the q_b* ray was
one of the stripped contact rays; both arm order counts of rᵢ are
units at q_b*. The two arm counts at q_b* itself are also prime
to q_b*: q_b*>76176 and each count is divisible by 4 and lies
strictly between zero and 2q_b* by Hasse.

Start with the final compatible index progression containing
q_b*, r₁ and r₂, but delete the q_b*-power from the index modulus
and delete its contact ball. This drops just its own added
contact-depth constraint: q_b* belongs to none of the earlier
index modulus, its own orders, or the order moduli of r₁,r₂
by their actual selections. All other order divisibilities and
real-open test remain. The actual q_b* now meets the finite
order caps of the reduced anchor, since the original final
progression satisfied both its point-order congruences and the
whole reduced anchor. It does not have to be a permitted output
of the numerical search again.

Use the same finite-clone source with the reduced anchor and
**actual reference pilot q_b*** (hence its actual counts and
marked point-order Frobenius). Strip all still-retained contact
primes from its order layers, so at these primes one may
independently copy the original q_b* norm signs. The reference
itself avoids μ₄ at these primes: this was chosen for the old
contacts and q_a at its original selection and for r₁,r₂ by
the new finite exclusions. At the remaining fixed modulus
clone the actual π_b* generator. At fixed primes dividing B this
gives the same every-place squareclass for the two possible
b-clones and keeps the old saturation. Preserve the new pair
balls by choosing the in-place q_b* norm character at r₁,r₂.
At the new q_b contact one has t square and the opposite factor
unit square by reciprocity (a and d are both square there),
and the derivative of w² at a root of t permits a simple
positive t-contact with the new correct stripped unit. More
explicitly (a/q_b*)=+ from the original construction and
(d/q_b*)=+ from the pair switch, and these symbols persist
by the chosen signs at p_a,q_a,r₁,r₂. The literal δ symbol
at q_b remains + by the unchanged rational phase modulo 8B.
The full original proof again supplies an order-compatible h
by CRT and accepted real progression, not a global w.

## 2. The whole switched normalized space is fixed

Use the old normalized unswitched space V, which is independent
of the b-clone under identical fixed/support phases and the
old local rules. Define V⁰ as its common local-evaluation kernel
at r₁,r₂ (the original identical evaluation also persists).
In the pair-switch proof the switched space normalized at its
b-clone is
```
V′ = V⁰ + { χ_d T + χ_a C(T) : T ∈ E[2] },
```
where C is the common unramified evaluation of the old
rational torsion at r₁,r₂. It is literally the same C for the
two b-clones, since their ratio is square at both rᵢ by the
prescribed norm signs. Therefore V′ is the same subspace of
global normalized squareclass triples, not just an abstract
isomorphic space. Its two dimension drops (old lines 0,t)
are unchanged. The normalized mark is the same cocycle
F_*=(t,aδ,atδ), as in the exact pair-switch proof. Each member
of V′ is trivial at its own moving q_b, including the
reference: for V⁰ this is old normalization; for the extra
classes it is the local squareness of a and d. All the fixed
places at which two clone parameters must have square ratio
include B, p_a,q_a,p_b,r₁,r₂ and infinity; they have been included
in §1. The two true elliptic curves in Smith's comparison are
twists of the fixed E_{a p_b d} by q_b*,q_b, not a comparison
of unrelated paired generators.

## 3. The same two central inertias tune the switched marked row

At p_a, all order torsion/Kummer layers are unramified
after stripping the retained contact and the only ramification
in the order governor is an abelian ray. At 2399 the actual XVI
anchor is prime to 2399; the original q_a group counts are
1645,2144 modulo 2399. The provisional q_b* and the two rᵢ
retain the p_b Gaussian modulus at 2399, so their group
counts there are 1854,1621 modulo 2399. Neither of these
pairs vanishes, the four distinct contact primes differ from
2399, so 2399 has never entered the index modulus. Thus the
same exact second central inertia survives. In both cases
the relevant centrality is over G=Q(i).

The exact previous marked row argument (45899b89…) now applies
with V′ in place of V. For clarity its annihilator proof does
not use the old hyperbolic block. On G_G, taking commutators with
the two inertias whose evaluations under F_* are independent
forces an annihilated F to be JF_* for a Weil-self-adjoint J;
on G_Q the correction is χ_{−1}v. The real and 2/3 local
lines are still the same, as d is square there and the same
normalized F_* is used. They leave only multiples of F_*
or that plus (−aδ,1,−aδ). The latter tuple has a forbidden
odd first-coordinate valuation at the fixed ℓ|P: the
0-root is separate with S,T colliding, and d is square at
ℓ. Thus the annihilator is exactly <F_*>.

Choose primitives for the cup of the actual F_* with a basis
of V′ in the fixed Selmer comparison, as in the original
[Smith, Theorem 3.2, proof (3.1)–(3.3)](https://arxiv.org/pdf/1607.07860).
These give its pairing variation by the Frobenius changes.
The central commutators are trivial in the actual order
governor and in all cocycle fields. Their evaluations span
(V′/<F_*>)^∨ by the preceding annihilator calculation.
Use this span to cancel the whole reference marked functional
at q_b*, retaining the order/ray data and prescribed normalized
splitting. The Gaussian Chebotarev plus coprimality tail proof
is unchanged, since the added governing fields are ramified
only in the fixed finite set and the finite new class has
positive density. This supplies an actual replacement q_b.
Cassels pairing annihilation against every normalized row
is annihilation against full Sel₂ because the omitted
rational torsion rows are always radical. The exact
Cassels pairing criterion therefore gives the switched
literal mark in the full Sel₄ image.

Nothing here makes the replacement H′ hyperbolic, tunes
all pairings between other rows, or implies that the
Sel₄ lift comes from a global point. The pointed genus-17
third-contact theorem does not follow from this ordinary
switched re-tuning without separately extending its local
targets and governing conditions.
