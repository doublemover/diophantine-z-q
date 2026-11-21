# The whole selected ramified jet is one prime-index harmonic theta coefficient

This is a coefficient identity for the actual selected *whole* signed sum, not for
a sum over labels selected because their values are known. The series below is fixed
once the first two actual variable primes and a finite level-root convention are
fixed. Its supersingular weights are actual modular differential values, not supplied
numerically. Neither the identity nor the two individual anchors proves that any
production coefficient is nonzero.

## 1. Literal data and the actual oriented embedding fibre

Keep the ordinary squarefree level N=205042530, the semistable elliptic curve
Eflat, its normalized newform, the fixed p=p_a=415721, and the same exact
selection of q_a,q_1,q_2 from 70410179 (including its three Selmer pairing bits,
two Gaussian tails, and all old local conditions). Write

    r=976393=11·37·2399,   h=2207,   h'=-h,
    a=q_a, b=q_1, q=q_2,   M=h r p a b,
    D=p a b q,   d'=rD,   Δ=-Mq.

Here the positive a,b abbreviate only the **two older moving primes**, not the
squareclasses called a,b in the contact equations. Both are fixed after their
actual selection. The squarefree fundamental discriminant Δ is odd; the
cyclic level mark is split at 2,3,5,7 and ramified at 11,37,2399. The genus
character is the pullback of the fixed idele character χ_{-2207} via the norm.
The positive-valued source of the selected twist is d'; the lower semistable
trace, its primitive based map and its chosen local square-root conventions
are those in 3927abd5, 124f1017 and ffa5c2e0.

For every geometric supersingular **marked** label s at p use an F_{p²}-model,
its actual Eichler order R_s=End(B_s,C_N), and the Gross lattice

    L_s=(Z+2R_s) intersect tr^(-1)(0),    Q(v)=Nrd(v).

An oriented conductor-one embedding sends sqrt(Δ) to v with Q(v)=Mq.
Conversely such v has odd scalar part and (1+v)/2 is in R_s.
It gives the actual maximal CM order in both adjacent maximal orders, so
conductor one at source and target. At a split level prime require the
eigenvalue of (1+v)/2 on the literal C_l to be the one in the chosen CM ideal.
At 2 reduce the **integral** (1+v)/2 on C_2; v mod 2 alone would lose this bit.
There are finitely many possible eigenvalue tuples in F_2×F_3×F_5×F_7;
one can restrict to the actual subfamily having any one tuple, or keep a finite
book of one coefficient series per tuple. This only partitions the selected
family, and does not claim that an arbitrarily specified tuple has a positive
density. Both ordered choices at any one split level prime are available in the
CM construction; the formula below fixes one and never sums across them.

Here is why this restriction counts exactly, not up to conjugate pairs.
In the notation of [Cornut–Jetchev §§4.7–4.9 and Theorem 3.1,
Corollary 3.2, Remark 1](https://webusers.imj-prg.fr/~christophe.cornut/papers/liftings.pdf),
the reduction valency for both conductors one (p outside the level) is one:
both the class-field ratio and the local N_p(0,0,0) are one. The inert residue
orientation set S_0 in their Theorem 3.1 is **empty** for this ramified p.
The norm index formula (21) also makes this transparent: powers of the
ramified CM uniformizer run through every integer lattice/crystal index,
instead of just even indices as for an inert CM field. In local double-coset
terms B_p^×=K_p^× R_p^×, by the common valuation and the unit group of the
unique maximal division order. At places outside the level and p the local
maximal-order lattice is a fractional O_K-ideal (in the split case use its
two direct projections). At the ramified level primes it has the unique
stable mod-l line; at the split level primes the prescribed eigenvalue
selects precisely one of the two marked local classes. Thus the target of
the reduction in the stated fibre has exactly the one Pic(O_K)-orbit with
the prescribed orientations. Optimal embeddings over s are taken up to
R_s^×. All the actual marked automorphism groups are ±1: a nontrivial
order-three part has no eigenline on E[2], and an order-four part has none
on E[3]. These units act trivially on v. Finally v -> -v reverses the split
eigenvalues (including 0/1 at 2), so neither conjugate-vector division nor
a factor from enumerating +/- is needed. The chosen embedding of K at p
and its specified Lie action are the ones used for the ramified canonical
lift in ffa5c2e0 (Gross Prop. 2.1); the fixed localization on the actual
CM orbit is the same as the C–J reduction. This avoids invoking their
last, inert-only modular-curve specialization.

## 2. The exact genus weight is fixed local data, up to one common sign

Fix a reference adelic Eichler frame and label representatives g_s in the
finite ideles of the quaternion algebra. At h=2207, away from Np,
choose a fixed split maximal matrix frame for this reference order.
All local vectors are written in that frame using g_s. The reduction
U of v at h is nonzero rank-one nilpotent: v²=Δ is divisible by h exactly
once, so v cannot be in h R_s. Define

    e(U) = Legendre(det(w,Uw),h),    w outside ker U.

It is independent of w: on a kernel/image line generator e with
U(f)=t e, the determinant is -t times a fixed frame determinant
times the square of the f-coordinate. For any k invertible,
e(kUk^-1)=Legendre(det k,h)e(U).

For the chosen orbit base with adele g_0 and CM embedding ι, if ideal idele u
takes it to s, write ι(u)g_0=γ g_s k with rational quaternion γ and integral
unit idele k. In the common right frames the transported endomorphism
satisfies v_s=k v_0 k^-1. Taking reduced norms and applying the fixed
rational idele character χ=χ_{-2207} gives

    ψ(u)= χ(nrd g_s) e(U_s) / (χ(nrd g_0)e(U_0)).

Indeed χ kills nrd γ by the product formula, integral unit parts away from
h are invisible, and at h its restriction to units is the displayed
Legendre symbol. The diagonal norms in this equation are on **ideles**,
not a Legendre symbol of an unnormalized rational degree. This also makes
the formula covariant under changing a representative g_s. It is the
same nilpotent sign mechanism already verified independently in a432a3e5,
now at a fixed honestly ramified prime of a maximal CM order. Inverting
Artin makes no difference to its quadratic character. Define
g(s)=χ(nrd g_s); the denominator, possibly dependent on Δ, is one common
sign κ_Δ, not a sign that can be chosen for individual points.

## 3. Linear first-coefficient extraction and prime norm shaving

On each local division order at p let P be its maximal ideal, so P²=pR_s.
For vectors in P take c_s(v) to be the coefficient of z^p of the actual
reduced endomorphism on the chosen formal parameter. Endomorphism addition
is formal group addition. The displayed coefficient is additive because
cross terms in the formal law evaluated on two series starting at z^p
have degree at least 2p; integer multiplication scales the coefficient
by its residue. Members of P²=pR_s start in degree at least p², since
[p] has height two. Thus c_s:P/P² -> F_{p²} is linear over F_p with its
actual marked formal parameter, not the choice of a square root of -Q.
For actual degree-p-oriented terms this is precisely 124f1017.

Write F_s for the quotient of the actual normalized newform differential
by the first derivative of the local Hasse scalar (in the same frame).
This is exactly f_N/(2λ_s(λ_s-1) H'_p(λ_s)) in its Legendre chart.
Frame transformations of c_s and the Hasse derivative are the same:
invariant differential rescaling cancels in their quotient. Thus
F_s c_s(v) is unchanged by the fine chart. Use the fixed F_p-linear lift

    P_s(v) mod p = Tr_{F_{p²}/F_p}(F_s c_s(v))/2.

More precisely the right side is an F_p-linear function on the common
integral lattice L_s intersect P; choose ordinary integer coefficient
lifts in a basis there, then restrict to each branch lattice below. The resulting linear
polynomial P_s is homogeneous **harmonic**, independently of this lift.

At this p the literal genus value ψ(P_p)=(-2207/p)=+1 (P_p is the unique
ideal above p). Its action pairs v/F_s with the Frobenius-conjugated
scalar product. Consequently the whole J_p from 124f1017 is in F_p:
taking field trace /2 pointwise computes the very same sum. Equivalently,
on a two-element paired class orbit the extracted scalar is the *sum*
of its two values, not half that sum. This explains why the 1/2 belongs
to the field projection and not to the class counting. The independent
eightfold ramified **level** coset factor is unchanged, not divided out
in the formula.

We can make a coefficient at q itself without an index Mq. At p use the
linear lattice restriction v in P, forced by zero residue norm in the
field R_s/P. On the trace-zero lattice this sets its one-dimensional
trace-zero residue in F_{p²} to zero. At each l|r in the Eichler frame
mod l use zero diagonal, a linear codimension-one condition since
the matrix is triangular, traceless, and of zero determinant.
At t=h,a,b (none divides Np), use one branch per line W in F_t²,
requiring v mod t to be in the one-dimensional space of maps killing
W and with image in W. These are linear sublattices of codimension two
in the trace-zero reduction. Impose nonzero reduction there at the
finite coset-filter stage. A vector of the target norm is in exactly
one branch at each t: its rank-one nilpotent has image=kernel.
Congruences at the different primes are independent by CRT on L_s.
All vectors of each branch lattice L_{s,W} have Q divisible by M.
So Q'=Q/M is integral and positive on that lattice, and the desired
shell is exactly Q'=q. No square root has been taken in an index.
By CRT, [L_s:L_{s,W}]=p r (h a b)^2. The norm bilinear polar
Gram determinant on L_s is 32(pN)^2: extend 1 to a basis of R_s
and replace remaining r_i by 2r_i-tr(r_i), a determinant-8
substitution with 1 orthogonal of norm-pairing 2.
Therefore the rescaled branch polar determinant is 32 p N² h a b/r.
Neither this determinant nor the count of branches suggests a small
explicit positive-definite table.

Keep the prescribed split mark, nonzero nilpotents and the fixed e(U)
as finite residue filters on each branch, encoded by cosets C of a
fixed multiple of L_{s,W}. For instance a multiple divisible by
4·3·5·7·h a b suffices for the stated filters; an extra multiple of p
is permitted. The split orientation at 2 uses (1+v)/2 and hence v mod
4R_s. Omit inadmissible cosets and give every retained coset its fixed
nilpotent sign e_C at h. The fixed harmonic theta contraction is

    G(T) = sum_{s,W,C} g(s)e_C sum_{v in C} P_s(v) T^{Q'(v)}.

Here the F_p signs ±1 have ordinary integer representatives, and all
series have integer coefficients. Positive definite even-lattice
theta transformation with a linear harmonic polynomial
([Borcherds §4, Theorem 4.1](https://arxiv.org/pdf/alg-geom/9609022))
makes these discriminant-group components of weight 3/2+1=5/2.
Indeed any shift in L_{s,W} is in the dual of its scaled sublattice for
Q', whose polar form is integral. Fix the common kernel of the finite
Weil representations on the metaplectic group. The constant term
of every component, and every transform component at a cusp, is
zero since P_s(0)=0. No small scalar Γ₀-level, eigenform, plus-space,
integral model of the Shimura lift or residual Galois packet is implied.

For every eligible q on the actual branch with this tuple, the exact identity is

    [T^q] G(T) mod p = κ_Δ · J_p   in F_p.

Each vector on the shell has one literal oriented point and the same
genus sign via §2; finite field projection commutes with the signed sum.
The remaining single nonzero scalar giving the actual elliptic first
coefficient is 4·u_p·(sqrt(Δ)/sqrt(d'))/(Δ/p), as in 124f1017.
Thus nonzero here is a true additive residue test for the same twist;
the independently certified even auxiliary and Gross–Zagier then give
the rank-one consequence on that selected twist. No such coefficient is
computed here. With a fresh mover from ab822551 held fixed beforehand, the
same construction works if the other genuine primes still vary unboundedly;
for ψ(P_p)=-1 replace trace/2 by a fixed F_p coordinate on the
anti-invariant line, equivalently (z-z^p)/(2t) for fixed nonzero t^p=-t.
No uniform-in-mover threshold or joint nonzero of the four jets follows.

## 4. Actual sparse Hecke rows and why full conductor transfers add no anchor

Let l be a good prime distinct from p. A true marked l-isogeny e at s
with differential d_e for the chosen frames intertwines [p] on the two
formal groups. Comparison of z^p gives H_target=d_e^{1-p}H_source
on a tame local deformation, hence dH_target along that deformation is
d_e^{1-p}dH_source at the supersingular point. The Hecke trace of the
normalized elliptic differential is a_l times it (differentiate the
actual based elliptic trace; any cusp constants disappear). This gives
the genuine tangent row

    sum_{e out of s degree l} d_e^{1-p} F_target(e) = a_l F_s.

In the same matrix a dual arrow has inverse phase, since
d_e d_dual=l, a rational F_p unit. A horizontal arrow carrying an
endomorphism transports c_s by exactly d_e^{1-p}, by intertwining
the same oriented endomorphism. Thus the relevant rows are not
unweighted Brandt rows applied to arbitrary label scalars.
One can include true Atkin/sign rows and Frob relations (use F_p-linear
coordinates for the latter). A finite actionable certificate is an
equality of linear functionals on **all** the oriented label variables:
actual coefficient row = nonzero multiple of an anchor evaluation +
an explicit finite combination of such proven constraints. It implies
a nonzero sum when the anchor value is known nonzero and its multiple is
in the same field/phase. The row identity must eliminate all outside
terms; retaining only edges believed favorable is insufficient.

There is a narrow exact barrier for taking only whole CM packets.
At l∤pNΔ there are 1+χ_Δ(l) horizontal arrows. When split their
two Artin shifts have the same genus sign χ_{-2207}(l).
Every other arrow reaches conductor l and is the unique ascending
parent of that marked conductor-l point. This follows locally from
the l+1 index-l lattices: the stable split eigenspaces give the two
horizontal arrows, an inert Cartan gives none, and every nonstable
line has conductor l with unique ascending neighbor. The global
orbit sizes agree: the kernel of Pic(O_l)->Pic(O_K) has order
l-χ_Δ(l); no exceptional unit quotient since this Δ has only ±1.
Use the inflated original genus character and the same local
parameter; all these points are unramified *over* the fixed
ramified base at p. Their entire signed conductor-l derivative is

    J_l = (a_l-(1+χ_Δ(l))χ_{-2207}(l)) J_1.

Iterating at distinct fresh primes yields the products of these
scalars. The complete packet trace equations therefore do not
supply an independent nonzero evaluation: every value remains zero
when J_1=0, even with genuine nonzero individual terms. This only
limits that specific row span; incomplete/geometrically certified
boundary rows could still succeed. Neither of the two available
anchors comes with such a sparse link to the whole sum.

## 5. Exact target for genuinely noncanceling input

Existence now needs a nonzero coefficient of the **specified contraction**
G at one prime q in the same selected terminal family. Neither a nonzero
theta component, a nonzero absolute complex coefficient, nor infinitely
many nonzero fundamental-index coefficients substitutes for that
statement. Ordinary half-integral T(l²) acts within a squareclass of
indices, so its local recurrence does not change q into a new prime q'.
A general cusp-space theorem is insufficient already for g(tz) with
composite t>1: such a nonzero shifted cusp form can have all prime
coefficients zero. This is a counterexample to that inference,
not an assertion of such a support obstruction for this G.

For an explicit sufficient phase theorem let A(q)=[T^q]G mod p and
B_X the finite-ray-selected primes through X before the two Gaussian
tail exclusions (same actual Cassels/CM orientations, all with the
specified root tuple). Put ζ=exp(2πi/p). Then exactly

    # {q in B_X: A(q) ≠0}
      = (1-1/p)|B_X| - (1/p) sum_{t=1}^{p-1} sum_{q in B_X} ζ^{t A(q)}.

A positive lower bound larger than the removed tails would give the
desired selected q. For example one may prove an error strictly
below (p-1)|B_X| minus p times those tails in the sum on the right.
The cutoff in the two-tail proof must be chosen with a lower-bound
constant that survives that cutoff, or the theorem must apply
directly to the fully screened family. A real second moment of the
unreduced complex theta coefficients, a mod-p moment of individual
terms, or unweighted equidistribution of CM labels only measures
other data. In particular the known paired partial anchor gives
no lower bound for the above expression.

As comparison, [Saha's fundamental-index squarefree theorem, Thm. 2](https://arxiv.org/pdf/1106.5110)
is characteristic zero, with level/character assumptions and composite
squarefree indices permitted. Also [Burungale–Tian's horizontal
nonvanishing](https://arxiv.org/pdf/1712.01465) varies class characters,
not this prescribed real genus character along selected prime q.
Those primary results do not prove the stated input. The reusable
smallest positive tests are a certified exact coefficient for a
single fully selected q, or one genuine full dual row as in §4.

## 6. Literal small normalization pilot (not a new theta coefficient table)

The checked CM15 whole-jet proof 1b2ade9e provides both actual oriented
X0(32) labels at p=5. In its short frames over F25 with rho²=2,
the degree-five coefficients of sqrt(-15) are 1+2rho and 1-2rho.
The second is Frobenius conjugate with the same root in the CM field.
The relative Type-I sign is (-3/2)=-1 (equivalently the determinant
of the actual horizontal isogeny in compatible Weil frames at 3 is 2,
so the local nilpotent signs have ratio (2/3)=-1). The based map
has ratio of differential to Hasse derivative equal to 1/4 at both
frames: its displayed actual cotangents are obtained by multiplying
the A-coordinate differentials by 2/4, while the Hasse derivative
in A is 2. The weighted c contraction is therefore rho. It is
anti-invariant, with field-coordinate projection (z-z^5)/(2rho)=1
on that total and exactly one half per already projected summand.
The common scalar 4rho/(-3) then gives 4 in F5, agreeing with the
separately certified [4] cusp coordinate on the actual rational E5.
This tests the pointwise projection-versus-pair factor and the
relative genus sign. It is **not** a second independent geometric
calculation of the classes, nor does it evaluate G at any q.

The standard-library replay checks that control and the complete
finite nilpotent/frame-covariance law at 3, with two illustrative
actual sign-filter frames at 2207. The latter are matrix-law controls,
not claimed reductions of selected CM labels:

    python3 -B check_signed_jet_phase.py | cmp - EXACT-SIGNED-JET-PHASE.json
    sha256sum -c SHA256SUMS
