# Exact opposite scalar Selmer matrices on the constant-conductor-15 receiver

Let d>0 be squarefree with d≡17 (mod 24). Keep the actual
conductor-15 pair and maps from the previous proof:

    E_d : y²=x(x+16d)(x+25d),     E′_d : y²=x(x−d)(x−81d),
    φ:E_d→E′_d,    ψ:E′_d→E_d,    ψφ=[2].

The scalar φ-Selmer group uses the x-Kummer **on E′_d**, and
the scalar ψ-Selmer group uses the x-Kummer **on E_d**.
This orientation matters. A positive nonsquare proper factor
β of d and its complementary θ=d/β are the original marks.
The receiver requires θ (equivalently β modulo the known
torsion class d) in the *rational φ-image*, not in the
local Selmer group alone.

Here we determine all scalar Selmer rows for these exact
models. This does not factor an actual d, certify any rank,
or replace the global rational marked condition.

## 1. Exact local scalar images

Brackets in the table denote local squareclasses. The local
x-Kummer includes the identity class 1 at O. For y²=x(x²+a x+b) its
value at (0,0) is [b]; both b here are squares.

| v | φ on E′_d | ψ on E_d |
|---|---|---|
| real | 1 | both signs |
| 2 | {1,5} | all unit classes |
| 3 | all classes | 1 |
| odd p dividing d | {1,d} | {1,−d} |
| 5 not dividing d, (d/5)=−1 | both unit classes | both unit classes |
| 5 not dividing d, (d/5)=+1 | 1 | all classes |
| other odd p | both unit classes | both unit classes |

The real claim is immediate from root signs and (negative)
real torsion on E. At any good odd p, valuations outside the
unit squareclasses are excluded by the equation: with p∤b the
valuation of the right side for positive x-depth is that of x
itself, and at negative depth it is three times that of x.
Over the residue field the two nonsingular curves are
isogenous with equal cardinality; the degree-two map has
two rational kernel points, hence cokernel of order two.
Hensel lift and the odd residue characteristic give the two
unit Kummer classes. This also proves the global support bound
at any p not dividing the corresponding b, whether or not
the other model is good.

For odd p|d, p≠5, each nonzero root has depth one. For v_p(x)<1
or v_p(x)>1 the remaining product is a unit square after
leading factors (the product of the root coefficients is a
square). Thus x must be square. At depth one the cubic has odd
valuation unless the stripped x is one of the two stripped
roots. Their stripped classes agree, since 1,81 and 16,25
are squares. The two torsion values attain the indicated
nontrivial class. At 5|d the same reasoning works on E′:
its two depth-one roots may coincide in residue, but still
force the same stripped x-class. On E the roots have depths
one and three. At x-depth two the total valuation is five.
At x-depth one or three the corresponding root must cancel
the otherwise odd total, giving x-class −d. Outside the
interval [1,3] the earlier leading-square argument applies.
This proves the p=5 ramified row as well.

At p=5 with d a unit, the E′ reduction is x(x−d)². Away from
the node x is square (or, if x has positive or negative
depth, the same valuation argument gives square). At the
node x has class d, attained by torsion, so this is exactly
{1,d}. On E the roots have depths zero and two, and valuation
one on x is possible only when 16d is square. For nonsquare
unit d this excludes any odd valuation; both unit classes
are attained by O and negative-root torsion since −1 is a
square at 5. For square d, normalize to d=1. Taking x=5
gives square right side 25·126 in Q₅ and the odd valuation
class; x=50 gives 25²·396 and the nonsquare unit class.
Their images generate all four classes.

At p=3 the twist residue d≡2 makes the nonzero collision on
E have centre −16d≡1. At an integral x in that residue
class x is square. At every other integral x the nonzero
root factors, after stripping trivial multipliers, have
the same nonzero residue, so x must be square. A negative
depth again has leading x³. Thus the ψ-image is trivial.
On E′, the value x=d gives the nonsquare unit class by
torsion and x=3 gives right side
9(3−d)(1−27d), a square in Q₃, giving the other generator.

At 2, d is square. On E′ after normalizing d=1, for v₂(x)>0
the factors (x−1),(x−81) have equal odd residue mod 8 and
square product. The same holds at negative depth for
(1−1/x),(1−81/x) after stripping x². So x is square in
either case. For the odd units x≡3 mod4, the ratio
(x−81)/(x−1)=1−80/(x−1) is 1 mod 8, forcing x itself to
be square, a contradiction. Thus the only possibilities
are 1 and 5, and x=5 gives square right side 16·(−95).
For E use the good model
Y²+XY=X³+((41d−1)/4)X²+25d²X, where x=4X.
For v₂(X)>0 the RHS depth is v₂(X); either Y² dominates XY
or their minimum depth is at least 2v₂(X), so v₂(X) must
be even. For v₂(X)<0 the analogous leading equality is
2v₂(Y)=3v₂(X). Every odd unit X is attained: the RHS is
0 mod 2 and the derivative of Y²+XY with respect to Y is
odd, so Hensel applies. This completes the exact table.

## 2. Global matrices and the transpose

Index p₁,…,p_m by the support of d. Work over F₂ with
additive Legendre characters. Set

    r_i=[−1/p_i],  t_i=[p_i/3],  ℓ_i=[p_i/5] when 5∤d,

and let M be the Laplacian with off-diagonal entries
M_ij=[p_j/p_i] and diagonal the row sum of its off-diagonal.
Thus (M a)_i=Σ_{j≠i}(a_i+a_j)[p_j/p_i].

For φ, the positive global representative is
3^u · Π_i p_i^a_i, since b′=81d². At 2 it must be 1 mod 4,
so u=rᵀa. At p_i the table says M a+([3/p_i])_i u=0.
Quadratic reciprocity gives [3/p_i]=t_i+r_i. Therefore

    A=M+(t+r)rᵀ

is the full matrix except possibly 5. If 5|d, that place is
already a row among the p_i. If 5∤d and d nonsquare at 5,
there is no new restriction on φ unit classes. But if 5∤d
and d square at 5, there is one additional row:
ℓᵀa+u=0, namely (ℓ+r)ᵀ. Call this last case the augmented case.

For ψ the global representative is
(−1)^s 5^v · Π_i p_i^a_i, with v=0 except in the augmented case:
the table killed the possible 2 factor and outside the augmented
case there is no new 5 factor. At 3, s=tᵀa+v. At p_i the
required class is (−d)^a_i; the stripped unit comparison is

    M a + diag(r)a + r s + ℓ v = 0,

omitting the last term when v=0. Off-diagonal reciprocity gives
Mᵀ=M+rrᵀ+diag(r). Thus the unaugmented matrix on ψ is precisely

    Aᵀ=M+diag(r)+r tᵀ,

and in the augmented case the extra column is ℓ+r. The matrices
are exact transposes, including the last row/column. All
exceptional phases and old ramified 5 are included.

Consequently

    dim Sel^ψ = dim Sel^φ + 1_(5∤d and (d/5)=+1).

In the prepared profile this extra-one case is exactly root
sign −. In particular it is **not** the opposite extra-one
orientation. For the literal a=0 scalar, 5|d, so the
dimensions are equal, without any assertion of the full
support needed to compute the common value.

## 3. Exact rational saturation gates, with all missing inputs explicit

Both original classes β,θ occur in Sel^φ for admitted
parameters, and d is the nontrivial torsion φ class. The two marks have
the same nonzero class modulo d; equivalently β and d span a
two-dimensional subgroup. The scalar ψ-image
contains its nontrivial rational torsion class −d. Writing
Rφ=E′_d(Q)/φE_d(Q) and Rψ=E_d(Q)/ψE′_d(Q), exact
complementary descent gives

    dim Rφ+dim Rψ = rank E_d(Q)+2.

Indeed the ψ map gives the middle comparison with E_d(Q)/2:
its potential kernel E′[ψ]/φ(E[2]) is zero since E_d[2] is
fully rational and φ’s image of it is E′[ψ]. Rational
image rank uses actual Mordell–Weil rank, not 2-infinity
Selmer corank.

For the unaugmented admitted case (including actual a=0),
the minimum Selmer dimensions are (2,2). **If** these exact
minima and rank at least 2 were independently proved, both
rational images would exhaust their Selmer groups, giving
the exact θ mark. Rank one would not suffice by this argument.

For the admitted augmented case the minima are instead (2,3);
a proposed rank-one saturation from dimensions (2,1) can't
occur. Rank at least 3 with those minima would suffice. There is
also a narrower one-bit alternative: if the two independent
ψ classes modulo rational torsion pair nontrivially under
the actual classical alternating Cassels–Tate self-restriction
on their images in Sha(E′_d)[ψ], then the ψ-rational image has
dimension just 1. This follows because a nonzero alternating
pairing on the two-dimensional quotient has zero radical
and rational images map to zero in Sha. Any independently
certified rank at least 1 then forces Rφ dimension ≥2, giving
θ at the exact φ minimum. This is a *conditional test*; no
such Cassels bit, actual rank, or Selmer minima are supplied
for the original pole. No finiteness of Sha is necessary
for this conditional rank-to-mark implication.

## 4. Exact finite controls

The replay enumerates the direct local scalar representatives and
the exact transpose kernels, including a ramified 5 example, two
small unaugmented marked profiles, an augmented profile rejected
by the p5 marked test, and an augmented numerical Ready profile
with β=17·73, t=60/20003 and θ=15131492551631281. That last
profile has the predicted exact sampled minima (2,3) and its
mark follows from the direct rational t-construction; it is
**not** a linked source pole. This replay does not infer any
rank from local matrices.

    python3 -B replay_transpose.py | cmp - EXACT-TRANSPOSE-SEL-CONTROLS.json
    sha256sum -c SHA256SUMS
