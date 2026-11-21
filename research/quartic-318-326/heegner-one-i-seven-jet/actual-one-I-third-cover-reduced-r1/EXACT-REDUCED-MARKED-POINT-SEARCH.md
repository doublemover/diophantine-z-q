# Exact archimedean reduction and local-lattice search on the actual ξ-lift

The fixed original curve is `E_d:y²=x(x−d)(x+3d)` with
`d=204618888056724185·114649·119851`. Use the already frozen
globally minimal pair of quadrics for the actual `ξ=1066808945`
relative lift through the negative split. The new square
variable basis and the pair of new equation rows are **integrally
unimodular**. They reduce the maximum coefficient from
145243861686420236632126 to 181008208, a factor greater than 10¹⁴,
without changing this rational curve, its minimal discriminant or
any earlier maps.

## Genuine exact reduction, and the destination is the original mark

Let A,B be the two actual Hessians before the new changes, and use p=114649,
q=119851, β=204618888056724185. The exact pencil is

```
F(a,z) = det(a A+z B) = β(p a²−q z²)(9p a²−q z²).
```

This exact determinant also gives a useful direct back-map. In
[Cremona–Fisher–Stoll, Lemma 4.6](https://www.dpmms.cam.ac.uk/~taf1000/papers/minred-234.pdf#page=22)
the adjugate-of-adjugates identity gives the Hessians of quadrics T₁,T₂,
and the map to `Y²=F(a,z)` has coordinates `(a,z)=(T₁,−T₂)) and
`Y=¼ Jac(Q₁,Q₂,T₁,T₂)` with the CFS notation. The resulting genus-one
morphism is defined everywhere. Neither a=0 nor z=0 can occur for a
rational point of that quartic because β is nonsquare, and Y=0 would
force a rational square q/p. From this literal determinant quartic, put

```
P=pq,
A_mark = 3p a/z,
V_mark = 3p Y/(β z²).
```

Exact substitution gives `β V_mark²=(A_mark²−P)(A_mark²−9P)`: this
is exactly the original marked quartic, not just a curve with
equal invariants. Setting `U=(A_mark−3P/A_mark)/2`,
`W=(A_mark+3P/A_mark)/2`, `Z=V_mark/(2A_mark)` gives
`U²−β Z²=P` and `W²−U²=3P`. The actual marked point would be
`(βU², β²UZW)` on E_d. Here all three factors of y are nonzero
(Z because Y was nonzero, U and W from their squared identities).
The exact good reductions at 7 and 53 have 8 and 52 points;
prime-to-place torsion injection with both cross exclusions gives
exactly the four rational two-torsion points in E_d(Q). Thus any
rational point of our tested model would certify the same marked
**nontorsion** point, independently of finite Heegner or theta residues
and without assuming finiteness of Sha.

For the reduction itself we use [CFS Lemma 6.8](https://www.dpmms.cam.ac.uk/~taf1000/papers/minred-234.pdf#page=46).
The four real roots are ±sqrt(pq)/p and ±sqrt(pq)/(3p). At each root
the exact matrix of the CFS rank-one quadratic square is checked
from the adjugate identity. The relative absolute derivative weights
between the two pairs are 1 and sqrt(3). Adding the two real conjugates
in each pair yields rational matrices G₀,G₁, so the Gram matrix can
be worked with exactly as `G₀ + sqrt(3) G₁` in Q(sqrt(3)).
The numerical search to discover U is not part of verification:
the checker proves positivity of the four Gram–Schmidt norms,
size reduction and every Lovász inequality at δ=3/4 by exact sign
tests in this quadratic field. Exact integer matrix multiplication
verifies U and V and the reduced polynomial rows. The determinant
of U is −1 and of V is +1.

## An exact finite search result, with a different height than the old A box

We searched this reduced four-coordinate model at primitive
integer projective height at most **25000**, not at height 25000
in A_mark. No rational point was found or inferred.

The implementation uses the [Elkies/Heath-Brown p-adic
point-search method described by Fisher, §6.2](https://www.dpmms.cam.ac.uk/~taf1000/papers/sixandtwelve.pdf).
Here is the exact finite lattice argument. Fix a smooth projective
point of the model modulo a good prime r=59 and normalize its last
nonzero projective coordinate to 1. Pick two dependent coordinates
whose Jacobian minor is a unit modulo r; the fourth coordinate is
the local parameter. Every integral affine point over that residue
is determined modulo M=r² by its parameter (one new radix-r digit).
For each of the 64 distinct residue points use those 59 residues
and Hensel-lift the two dependent coordinates further to a vector
v modulo M² on which both quadrics vanish. The normalized coordinate
of v is exactly 1. Fix the corresponding parameter coordinate
of v to the chosen representative even during this second lift.

Let w be the solution to the simultaneous homogeneous tangent
equations modulo M, with projective coordinate zero and parameter
coordinate one. If a primitive rational vector x reduces to the
chosen class modulo M, then `x=x_i v+M y` with pivot coordinate
`y_i=0` and x_i a unit modulo M. Expanding the two homogeneous quadrics
modulo M² and cancelling x_i gives precisely the tangent equations
for y modulo M. The lattice containing x therefore has ordered basis

```
v, M w, M² e_j, M² e_k
```

where j,k are the dependent coordinate indices. This has determinant
±M⁵ by pivot and parameter normalization. Replacing its basis with
an exact LLL basis is independently verified unimodular for each
lattice. Every vector in the projective box is inside the Euclidean
sphere with squared radius 4·25000². The code uses rational
Gram–Schmidt and exact integer-square-root interval enumeration
in that sphere; the final equality test is exact. Thus the empty
output is complete for this box, not a floating shortlist of
shortest vectors or a selected single residue. There were 3776
lattices, 231524 short vectors counting zero and signs across
lattices, and 42578 primitive vectors within the coordinate box
counting signs. The zero point is excluded by primitivity.

## Reproducibility and scope

Python 3 and SymPy 1.14 were used. The exact minimization JSON of the
sibling pack is an immutable input; the first checker also accepts
that JSON as its positional argument. Runtime for the finite
box was about 20 seconds. No global height bound is claimed, no
rational point or rank follows from this empty search, and no
statement is made about the distinct companion dθ.

```sh
sha256sum -c SHA256SUMS
python3 -B check_cfs_reduction.py | cmp - EXACT-REDUCTION-REPLAY.json
python3 -B check_point_box.py | cmp - EXACT-REDUCED-25000-BOX.json
```
