# The actual CM15 jet follows from four weighted Hecke rows on eight vertices

This is a finite check on the same genuine X₀(32)/F₅
and the same two distinguished CM labels of the full
CM15 canary (manifest 1b2ade9e1ed33302ffdf7a6787df459f54cefb3d9898e43a1d5c45a71b49c660).
Unlike that exact global-coordinate proof, the positive
certificate here can avoid reconstructing the eigenline
or evaluating the other eight supersingular vertices.
For an independent hard check the replay also evaluates
the **actual q-normalized** weight-two function in all
16 frames by explicit chart derivatives. No substitute
modular function or selected production curve is claimed.

## 1. Ordered finite labels and true normalized function

Over k=F₅(ρ), ρ²=2, the supersingular source has
j=0. Choose A₀:y²=x³+1 and ω=dx/(2y) on its
fixed short model. Over k all 2-torsion is rational;
every normalized 2-isogeny from a short j=0 model
with B∈F₅× has target j=0, B′=2B, so all succeeding
2-kernels are visible over k too. The five-step
directed, nonbacktracking degree-two chains comprise
all 3·2⁴=48 cyclic C₃₂'s on this same E. This is a
classification by the kernel of the composite; a
backtrack composes a 2-isogeny with its dual and
creates noncyclic two-torsion. Aut(E)/± is of order
three and acts freely (already no invariant line of
E[2] for an order-three automorphism). We find exactly
16 distinct moduli points with three chains each.

For a short model y²=x³+A x+B and kernel (r,0), write
b=3r²+A. The normalized short Vélu maps are

    (x,y) ↦ (x+b/(x−r), y(1−b/(x−r)²)),
    A′=A−5b, B′=B−7rb.

The immediate dual kernel in the next model has
x=−2r. For three successive kernel x values (r,t,u)
write v=(t−r)/2, v′=(u−t)/2. The marked t8
coordinate is

    T₈=32v/(v′−4v).

Indeed the tower formulas of the full canary start
with the actual order-four x distance v: the first
2-isogeny sends that point to x=r+2v. For a generator
P₈ the normalized order-eight expression in the
original model is S=(x(P₈)+x(3P₈)−2r)/v. Addition
of the first kernel translates x−r to b/(x−r),
so the normalized image after the next marking has
distance v′=(S−2)v. Substituting into 32/(S−6)
gives the displayed rational expression. This also
proves it in the infinitesimal tame lift. This use
of marked kernel x values remains valid at j=0,
where solving a forgetful t2 equation by division
would lose the label (e.g. T₂+16 can vanish).

For a length-four window the corrected t16 formula
is T=(B₈−2 A₈)/(A₈+4), with A₈,B₈ determined
by the two adjacent length-three windows. Let
U=T₁₆(z), V=T₁₆(2z) from the two length-four
windows of the same length-five chain. On the
[Tian pointed model, Proposition 2.1](https://archive.ymsc.tsinghua.edu.cn/pacm_download/232/8762-35_Ye_Tian_Congruent_Numbers_and_Heegner_Points.pdf#page=6)
X=T₁₆(2z)+2, and full Fricke is (2,4)−P.
The identity T₁₆(z)T₁₆(−1/(16z))=8 is Maier's
Fricke eta formula; thus x((2,4)−P)=2+8/U.
Combining these two **ordered** coordinates gives

    X=2+V,
    Y=((X−2)²(4+X+8/U)−X³−4X−16)/8.

This identifies the literal ordinate, not ± chosen
anew for each label. The quantities inverted above
are units for every one of the 48 chains. Their
actual mod-5 distinctness and the curve equation
are checked in the replay.

To evaluate the true form, use the dual-number
family A=e, B=1, e²=0. Each kernel x root lifts
uniquely by the simple cubic derivative, and the
same normalized ordered chain formulas give
X(e),Y(e). In the above choice of y, Y=+q⁻³+…:
indeed x((2,4)−P)−2 has leading 8Y/X² at
infinity, and 8/T₁₆(z)=8q+…. Thus dX/(2Y)
has initial coefficient −dq, and its negative is
f₃₂(q)dq/q: genus one and the standard normalized
first coefficient characterize the differential.
The canonical Kodaira–Spencer expression in the
Weierstrass frame `ω=dx/(2y)` is

    KS(ω²)=(2 c₄ dc₆−3 c₆ dc₄)/(1728 Δ).

For normalization, on the Tate curve c₄=E₄,
c₆=−E₆; the two Ramanujan derivative identities
give exactly dq/q for the displayed expression.
It is horizontal under scale change and therefore
descends, so this equality on the q-chart pins the
same differential identically. With c₄=−48A,
c₆=−864B, Δ=−16(4A³+27B²), on our dual chart
at (0,1) this is de/6. Consequently the actual
q-normalized form value in its true fixed
Hodge frame is

    f₃₂(P,ω)=−6 · [e]X(e)/(2Y(0)).

The branch is a legitimate tangent chart: Hasse
on y²=x³+A x+1 in char5 is 2A and has nonzero
first coefficient; the tame extra cyclic marking
is finite étale on the stack. There are no new
choices of the sign of the normalized differential
in this computation. The three chain representatives
of any one pair may differ by a scale and **do not**
have identical weight-two values before changing
frames. The replay explicitly verifies the
covariance under all three such choices.

## 2. Make every T₃ arrow weighted and marked

The four cyclic order-three subgroups of the source
are rational over k: all eight points are on
x=0 or x³=1 from the exact 3-division polynomial,
and their y squares 1,2 have roots in k. For each
such subgroup use its normalized short Vélu
3-isogeny. Carry the first (r,0) of the 2-chain
to the image kernel point. Going to the next stage
by the two commuting quotients, transport the
3-generator by the first 2-isogeny and repeat.
Since the two normalized composite isogenies have
the same commuting kernels and differentials, both
short common targets have identical coefficients;
the checker confirms those coefficients at each
stage. This computes the actual image C₃₂ rather
than a new arbitrary cyclic subgroup.

After quotienting by the order-three kernel the
first short coefficient B_t is in F₅×, with A=0.
Choose a scale s with s⁶=B_t in F₂₅ and divide
the target x-coordinates by s². To change to
the chosen representative frame of the moduli
pair there may be an additional sixth-root
scale u. The derivative of the whole normalized
map into the chosen target model is then su.
The actual weight-two term in the Hecke row is
(su)²/3, exactly as required to compare the
chosen source and target Hodge frames. The replay
independently checks the frame law across all
48 source chains. As extra controls it reverses
the 2-chains by dual kernels, gets the true
Fricke point (2,4)−P and verifies the −1
eigenvalue with the correct differential factor.
These checks are not needed for the sparse T₃
certificate.

The eigenvalue of f₃₂ at 3 is a₃=0 from
#(y²=x³−x)(F₃)=4. Therefore every computed
row R_i of T₃ annihilates the actual values
vector f, including rows indexed by i=1,3,9,11
below. We never use a₃ read from a numerical
q-series.

## 3. Four rows suffice, with one geometric anchor

Index the selected k-points lexicographically
by the pair ((X₀,X₁),(Y₀,Y₁)) in the basis
(1,ρ), 0-based; common source frames are given by
the first chain encountered in the replay.
The actual CM labels of the displayed +Y
convention are vertices (3,1) in weighted order.
For them the true ε=√5 tangent in the chosen
Hodge frame has coefficient of A equal to
r₀²(1−ρ), respectively r₀²(−1−ρ), by the
same T₂ derivative used in the full canary
(r₀ is the first reduced kernel x at that
vertex). Multiplication by 4 and the literal
degree-two modular isogeny of differential 2
then give the exact normalized jet functional

    L=(2+3ρ) e₁+e₃

on the q-normalized f vector; this includes the
minus sign converting f to the pointed model's
invariant differential. Here e_i is evaluation
in vertex i's chosen frame. The checked four-row
identity in the **actual** Hecke matrix is

    L − (3+3ρ)e₁ =
        (3+4ρ)R₁ + (2+4ρ)R₃ + (3+ρ)R₉ + (2+ρ)R₁₁.

Its entire support is vertices 1,3,5,7,9,11,13,15.
Only these four full outgoing rows are required:
nothing forces the other four targets to be row
sources or the chosen set to be closed under
all Hecke arrows. Since X₀(32) has genus one with
a smooth reduction at 5, a nonzero holomorphic
differential vanishes nowhere. Therefore the
q-normalized f satisfies f₁≠0 even without
computing its exact value, and the identity
certifies L(f)≠0 **without reconstructing an
eigenline or solving a graph-wide linear system**.
The direct evaluation independently gives
f₁=2+3ρ, f₃=2+3ρ, and L(f)=4.
The full 16-row replay gives rank15 for T₃;
omit row0 and append L to get determinant 1.
That is a different, denser positive witness.

## 4. What a sparse production certificate would need

At the actual fixed level 205042530 and any actual
mover p, finite selected rows of (T_l−a_l) need
only include every target of their respective
arrows. Two rigorous alternatives avoid solving
the entire production eigenline:

* An identity L−c e_x in their finite row span
  plus an independent anchor f_N(x)≠0 and c≠0.
* From the row relations and L(f_N)=0, deduce
  vanishing of f_N at more than 2g−2 distinct
  noncuspidal vertices. This contradicts the
  canonical divisor degree of the actual nonzero
  weight-two cusp differential on the smooth
  model. This does not require entire W rank one.

In the production level g=52531137 (index
630374400, 128 cusps, no elliptic stabilizers);
the safe threshold is 105062273 distinct zeros.
An even smaller direct comparison can use
a known exact normalized value in a fixed frame,
but the pilot's genus-one nowhere-zero anchor
does **not** carry over to this genus. Conversely
L in the finite row span certifies a zero jet, no
nonvanishing assumption. A finite overestimate
of the kernel of the chosen rows that admits
both values at L does not decide the actual L.
The whole geometric graph at historical p_a has
about 2.18×10¹³ vertices; the usefulness of
this finite-support test depends on finding the
actual relation or actual anchor, not on how
one names the graph. In particular, knowing a
scalar modular-unit coordinate that has multiple
aliases at a mod13 vertex does not identify this
weight-two value. No actual production jet or
original point is claimed.

Replay (standard Python; approximately 2 s):

    python3 -B check_x032_weighted_hecke.py | cmp - EXACT-X032-HECKE-JET.json
    sha256sum -c SHA256SUMS
