# Exact transvection image test for the actual 13-Selmer group

Fix the historical one-I base d=2811626664334219040035976315,
E_d:y²=x(x−d)(x+3d), V=E_d[13], and its full residual image
G=GL₂(F13) from the [exact point-field packet](../actual-one-I-cyclotomic13-r1/EXACT-POINT-FIELD-13-CERTIFICATE-TARGET.md).
Let L be its splitting field, F=Q(P) for the same nonzero point
and S the two primes of F above 13. Let Δ act by [a] on P and
let λ([a])=a. A class of F(S,13)_λ has all valuations off S
zero modulo 13.

This note gives an exact global descent filter on that ambient
Kummer space and a concrete independent test at the good prime
53. It does not compute the ambient class eigenspace, find a
global Selmer class, or bound rank.

## 1. The actual module and incidence filter

Use additive notation for the one-dimensional Weil-value module
μ=μ13. Let M be the space of functions f on V minus zero with
values in μ satisfying f(av)=a f(v). Its Galois action is

    (g f)(v) = det(g) · f(g⁻¹v).

The Weil embedding V→M is x ↦ (v ↦ e13(x,v)). This is equivariant
for the exact determinant twist, and its image consists of
linear functions with values in μ. The full function module
without homogeneity is coinduced from the actual point stabilizer
with coefficient μ. Shapiro and the scalar projectors identify

    H¹(Q,M) = (F×/F×^13)_λ.

The λ direction is positive: for any lift σ with σP=aP,
the Shapiro evaluation of the commuting map f(v)→f(av)
amounts in cohomology to the natural field action σ on F.
Equivalently, evaluating a global cocycle at aP gives a
times its evaluation at P.

In the un-twisted covector space V* let M_c be functions on
nonzero c satisfying F(ac)=a⁻¹ F(c), again with values in μ
and with the corresponding determinant twist. Define

    (Jf)(c) = ∑_(v : c(v)=1) f(v).

There are 13 terms and no averaging. This map is equivariant
and has the required homogeneity −1. Using representatives
(1,t), (0,1) for the 14 projective lines in each argument,
the matrix is c(v)^11, with zero when c(v)=0: the only
contributing vector on the source line is v/c(v).

The rank is 12. One algebraic check factors the matrix through
evaluation of the 12 degree-eleven binary monomials and the
diagonal of binomial coefficients, all nonzero modulo 13.
The evaluation maps have rank 12 since a degree≤11 polynomial
on the affine chart cannot vanish at all 13 residues unless zero.
Every actual linear form has zero sum on every affine 13-line:
the constant and linear sums are both zero. Thus ker J is exactly
the displayed copy of V. Its image, after removing the value
twist, is the space of evaluated homogeneous polynomials of
degree 11 on covectors. This is irreducible: diagonal torus
weights of its monomials are distinct since their differences
are <12; from one monomial triangular unipotent substitutions
and weight projections produce a pure power and then every
monomial (all binomial coefficients are nonzero). In particular
M/V is irreducible.

For the cokernel, pair functions of opposite homogeneity
on covectors by summing their products over the 14 lines.
The pairing is invariant and nondegenerate, using bare F13
coefficients before twisting. The transpose of J is the
same affine incidence operator in the other direction. Its
kernel consists of linear forms on V*, the module V. Thus
the bare coker J is V*, and after twisting by μ it is V
via Weil. In particular the twisted cokernel has no global
invariants. The image of J has no global invariants either:
an invariant covector function vanishes at every nonzero
covector because its stabilizer has surjective determinant.
The long exact sequences therefore give an exact sequence
at both indicated spots:

    0 → H¹(Q,V) → H¹(Q,M) → H¹(Q,M_c).

For the last kernel statement, first use the cohomology
sequence for the image submodule, then use H⁰(coker J)=0
to inject its H¹ into H¹(Q,M_c).

Writing F^c for the field of a nonzero covector c, Shapiro
identifies the right term with its inverse-scaling Kummer
eigenspace. The exact test J(a)=0 is an unaveraged ordinary
norm: choose c with c(P)=1, and form the incident compositum
H=Q(P,c). It has degree 13 over F^c. Indeed the covector
stabilizer acts transitively on the 13 vectors c(v)=1,
with the simultaneous stabilizer of c and P diagonal of
order 12. On cochains the sum on this transitive orbit is
the coinduction-to-corestriction augmentation, so on Kummer
classes the right test is exactly N_(H/F^c)(a) a 13th power.
This statement neither assumes additive averaging nor
identifies the two nonisomorphic permutation modules.

For orientation, one can represent a covector of kernel
<P_0> as c(v)=log_ζ e13(P_0,v). In F_0(ζ), where F_0=Q(P_0),
the covector field over the line field is the fixed field
of simultaneous dilation [b] of P_0 and ζ↦ζ^b. It has the
explicit relative generator ∑_[a] σ_a(W)ζ^a. The 12 ζ^a
are independent over F_0 by the surjective determinant of the
point stabilizer; σ_a(W) are all distinct (verified on a
literal degree-one reduction at 53). Hence the sum has
orbit size 12 under cyclotomic dilation alone. The related
finite canary of this sum at 53 has one collision, so
no assertion about local monogenicity is made.

The point and covector fields have the same rational
permutation character as abstract representations:
fix-counts of a matrix and its contragredient agree.
Nevertheless their local ordinary 13 decompositions are
different: points (e,f)=(12,1),(13,12), covectors (1,12),(156,1),
as exactly checked from Borel and inertia actions. Nor
is there any equivariant isomorphism of the mod-13 full
permutation modules. The orbits on ordered pairs (v,c)
are exactly classified by c(v) in F13, so every equivariant
map is a linear combination of the thirteen incidence
operators with c(v)=t. They all kill the nonzero linear
submodule in homogeneity one. Equal zeta/permutation
characters cannot be used as an integral class-saturation
shortcut here.

## 2. No covector field needed: all good transvection primes suffice

Call a good prime ell a transvection prime if its actual
residual Frobenius is a nonidentity unipotent. These primes
have ell≡1 mod13. At such a prime the nonfixed nonzero
vectors form 12 Frobenius orbits of length 13. There is
one orbit of these primes under scalar dilation, so for
a λ class it suffices to use any one of their degree-13
point-field completions. The test is that its localized
unramified Kummer class there is zero, equivalently its
unit residue is a 13th power in F_(ell^13). If the input
valuation is a multiple of 13, remove that power first.

**Theorem.** A class a in F(S,13)_λ belongs to the image
of H¹(Q,V) in H¹(Q,M) if and only if it passes the above
test at every good transvection prime.

To prove necessity, represent the class by a global
V-cocycle. For any lift g of a transvection u, the
cocycle at g^13 is (1+u+⋯+u¹²) times its value at g.
On V the operator is zero since u=1+N, N²=0, and
13 and ∑_j j vanish modulo 13. Restriction to a
nonfixed point completion evaluates this zero.

For sufficiency choose a cocycle z in M representing a.
It has a finite affine Galois image through (z,ρ)
into M⋊G. On G_L its restriction is a homomorphism;
its image W₀⊂M is a G-stable F13-subspace. A chosen
transvection u may be written in coordinates as upper
unipotent. On the 14 homogeneous projective labels
its action is one fixed label and one 13-cycle, with
no scalar factors in the representatives (t,1) of the
moving cycle. The operator N_u=1+u+⋯+u¹² has rank one,
is zero at the fixed label, and is nonzero on the
moving orbit. It kills V and induces a nonzero linear
functional (up to the image line) on M/V. If W₀ is not
contained in V, irreducibility of M/V implies it
surjects there, so some w∈W₀ has N_u(w)≠0.
Vary a lift of u in the finite affine group by w.
The semidirect-product cocycle formula says the two
13th-power values differ by exactly N_u(w); hence
one has nonzero evaluation on the moving cycle.
Chebotarev applied to that actual finite affine
extension provides a rational prime with that
Frobenius conjugacy class, avoiding the finitely many
bad and ramified primes. Conjugation only changes
the chosen moving orbit representative, not zero.
At its degree-13 point-field completion z(g^13)
evaluates the unramified Kummer residue of a, a
contradiction. Indeed at a good prime away from
13 the ambient representations and all these point
fields are unramified; valuations zero modulo 13
make the Kummer local classes unramified as well.

Thus W₀⊂V. To remove an inflation obstruction, first
H¹(G,M)=0: it is a direct summand of H¹ for the full
point function module. Shapiro there gives H¹(H_P,μ)
with stabilizer H_P=(1,b;0,d). Its normal order-13
part is upper unipotent, and diagonal d acts on
Hom(U,μ) by d² (conjugate the argument by d⁻¹ and
act by determinant d on the value). Thus this Hom
has no invariants and H¹ vanishes. Also H²(G,V)=0
by the central element −I, acting as −1 on V and
trivially by the simultaneous inner action on
cohomology. The exact sequence for V⊂M gives
H¹(G,M/V)=0. The quotient of z in M/V, being zero
on G_L, inflates from this zero group. So z lies
in the image of H¹(Q,V), proving sufficiency.

After this exact global descent the only additional
Selmer condition is the old formal 13-place test at w+.
At good primes away from 13, inertia acts trivially on V;
all evaluation components are unramified by the S condition
and their joint point evaluations detect a nonzero vector.
At every actual bad prime and infinity H¹(Q_ell,V)=0
by the previous exact local packet. At 13, evaluation at
a formal nonzero P kills V⁺ and identifies V⁻ with μ over
F_w+. The completion has degree 12; restriction on H¹
with coefficients V⁻ is injective by corestriction.
Thus zero evaluation at w+ is equivalent to being in the
ordinary kernel of the map to H¹(Q13,V⁻), the true local
Kummer condition. The w− conditions of the earlier ambient
upper bound remain valid useful rows, but are not needed
once global descent has been proved.

## 3. Exact actual 53 diagnostic and finite scope

The actual curve has #E_d(F53)=52, repeated residual Frobenius
eigenvalue 1, and Frobenius is not identity (169 does not divide
52). Thus 53 is a transvection prime. The replay factors the
true x polynomial over F53, chooses one of its six degree-13
factors, verifies irreducibility and the actual W residue,
and evaluates the nonfixed branch with no dual field. This
gives an exact new residue score for any already localized
global λ element. For the scalar projection of v the score
is zero, as sign-evenness predicts. For the literal class
eλ(2+W), whose twelve residues in that branch are units,
the exact score is 8 with the archived sign and generator.
This is a detection canary for the actual ambient map; 2+W
is not asserted to be a global admissible S-class. The
separate coinvariant calculation has point/covector dimensions
2,2 at this Frobenius; J and the genuine unramified V-image
each have rank one, confirming the additional row on the
full local ambient module.

Any finite set of such tests gives rigorous linear *upper-bound
rows* on actual Selmer classes when a global ambient dimension
bound and actual candidate vectors are certified. Conversely
the all-primes theorem plus finite-dimensionality implies
existence of a finite determining set, but neither the proof
nor this replay gives a numerical prime cutoff or a complete
finite certificate for the actual global space. It is not
a bound on the faithful class rank. No such rank bound,
point, or p-adic nonvanishing is claimed here.

    sha256sum -c SHA256SUMS
    python3 -B check_point_covector_incidence.py | cmp - EXACT-POINT-COVECTOR-INCIDENCE.json
    python3 -B check_actual_transvection_53.py | cmp - EXACT-ACTUAL-TRANSVECTION-53.json
