# One fixed biquadratic norm is exactly the two named conductor-15 admissions

This is a factorization-free **criterion**, not an evaluated norm.
It applies to the literal scalar or to the separately justified
retuned original specialization with the same visible rows.
Let

    δ = 1−β c²,   θ=[δ],   d=βθ,
    T = 131·6551·2470991·16782959 = 35589230039008870789,
    e = 5·11·17·1489·131·6551·2470991 = 2952271997968816765,
    L = 7129,     F = Q(√5, √e).

Here [δ] is the positive squarefree representative. Neither θ
nor the positive integer U=θ/T is assumed given. Its known
visible support is exactly the part at the primes of T; other
factors can be arbitrarily numerous. The actual β primes and
the four θ-local data used here are unchanged. In particular
δ/T is the exact rational circuit value with the known T
removed, not a squarefree factorization input.

The two previous named admissions are:

1. The specific 2-lift (θ,θ,1) of the φ mark is locally
   admissible. On this profile this is equivalent to θ a
   norm from Q(√5).
2. The particular signed odd scalar e is in the opposite
   isogeny Selmer group Selψ.

We prove both hold **iff**

    N_{F/Q}(η) = 7129 δ/T

for some η in F. In the basis 1,√5,√e,√(5e) this is the single
explicit rational equation

    (x²+5y²−e z²−5e w²)² − 20(x y−e z w)² = 7129 δ/T.

## 1. Opposite Selmer membership requires only hidden primes split in √e

At the eight visible β primes and the four visible θ primes,
check the literal local ψ group {1,−d}. The valuation of e
picks the class; the normalized unit of that class agrees
with the normalized unit of e at every one of these twelve
primes. This is checked directly using the twelve known
stripped d-unit bits, **not** by assuming U prime.
At 3 the ψ image is trivial and e≡1 mod3;
at 2 all odd unit classes are possible; at infinity the result
is automatic. At all good odd places not dividing d the unit
classes are the image. At a hidden p|U, e is a unit and
the only unit in the group {1,−d} is the square class.
Thus exactly the remaining conditions are (e/p)=+ for every
p|U. Independently the named θ-lift requires (5/p)=+ for
every p|U, since the four visible θ primes already split √5.

For the seven primes q|e, the known bits of the stripped
d units give (U/q)=− only at **17 and 2470991**:
divide the stripped d unit by the known factors of βT other
than q. Choose the fixed positive auxiliary prime 7129.
Its Legendre pattern at these seven primes is exactly the
same, and it is 1 mod24. It splits in both Q(√5) and Q(√e):
at 5 its residue is 4; for e use reciprocity at L≡1 mod4
and note that exactly two of the seven signs are negative.
The accompanying integer replay verifies the twelve true
local ψ checks, the two correction signs, and primality
of this fixed auxiliary.

It follows that for N=L U, the quadratic Hilbert symbols
(5,N)_v and (e,N)_v are both neutral at the fixed places:
at an odd q|e the unit residue of L U is square; at 5 this
also handles 5; at L both fields split. At 2, e≡5 mod8
so both are the same unramified quadratic character and N
is an odd unit. At infinity the two fields split. At every
other odd p the radicands are units. If p∤U, the symbols
are neutral, and if p|U they are exactly (5/p) and (e/p)
as required. This includes the possibility p=L, already
split independently.

## 2. Exact local-to-global, including the full group at 5

For a local abelian extension, local reciprocity identifies
the norm subgroup with the kernel of the reciprocity map
to its decomposition group. For this biquadratic algebra
that kernel is precisely the intersection of the kernels
of the two defining quadratic characters (5,·)_v, (e,·)_v,
also at split places. Hence L U is a local norm everywhere
exactly when the two named admission conditions above hold.

Hasse's cyclic norm theorem alone would not justify a
biquadratic norm. Here the decomposition group at 5 is
the entire V4: e/5≡3 mod5 is a nonsquare unit, independent
of the odd-valuation class 5 in Q₅×/Q₅×².
Tate's norm-obstruction criterion therefore gives the
Hasse norm principle for this exact field: the restriction
to that one local full group is the identity on H³(V4,Z),
so the obstruction kernel is zero. See the exact statement
in [Frei–Loughran–Newton, Theorem 6.1](https://pure.manchester.ac.uk/ws/portalfiles/portal/55657924/HNP.pdf).
Thus local norms give a rational global norm here.

Replacing U by δ/T changes by a rational square. Squares
are in the local norm groups (both characters have order
two), and hence are global norms here by the same criterion.
Norm transitivity proves the converse or, equivalently, use
the exact local norm characterization in the other direction.
This establishes the asserted equivalence with the raw δ
equation, no unknown factor count or factorization premise.

## 3. Exact use and limitation

One rational solution to this norm equation for the
**retuned** original specialization supplies both named
admissions, and its already-computed Θ₂(θ,e)=−1 then forbids
the conductor-15 rational mark. No independent crossed
denominator character or hidden-prime count is required.
On the **unchanged** original specialization one still
needs the exact crossed sign (D_exc/e)=+, as before.
A failure of the norm equation only rejects one or both
named admissions, not all other lifts or PointPair routes.
No rational norm solution, actual mark or rank is claimed.

    sha256sum -c SHA256SUMS
    python3 -B replay_fixed_admission_field.py | cmp - EXACT-ADMISSION-FIELD-CONTROLS.json
