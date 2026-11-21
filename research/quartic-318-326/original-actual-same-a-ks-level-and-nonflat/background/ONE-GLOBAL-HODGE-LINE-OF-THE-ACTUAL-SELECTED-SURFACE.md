# One global Hodge line of the actual selected D=210 surface

The existing local construction used an actual polarized scheme on the
proper 3 or 11 trait separately at each finite place. These are not
independent models: the actual common 33-mark assembles them to one
global good model on precisely the common height field L. This gives the
previously explicit identification of the native direction's normalized
Hodge degree with the same surface's stable height, at paper level,
and constructs the finite support of its norm from an actual lattice.

## Globalize the chosen generic sections, not a coarse isomorphism class

Let S=Spec O_L, where L already contains the same selected original
noncontact point and its actual full 3 and 11 marks, hence the chosen
full 33-mark. The selected A/L, its QM order and polarization are fixed.
Write S_N=Spec O_L[1/N] and X_N for the genuine proper fine PEL scheme
over Z[1/N], with its universal principally polarized abelian scheme.
These are the fine models in [Yuan v2 §2.1](https://arxiv.org/html/2205.11334v2#S2.SS1)
using the fixed discriminant-210 order and polarization element.

For N=3,11,33 the chosen generic point x_N extends uniquely to a
section of X_N over S_N (a morphism over Z[1/N]).
Indeed base change to S_N gives a proper scheme over this Dedekind
scheme. A generic rational point spreads over a nonempty open by
finite presentation. At any missing closed point the local ring is a
DVR, so the prescribed generic morphism extends there by properness.
[Stacks 29.43.5](https://stacks.math.columbia.edu/tag/0BX7) extends it to
an open neighborhood. The local extensions patch uniquely: the
diagonal of the target is closed and equality at the generic point
extends on any reduced integral overlap. Thus this is exactly the
previously filed proper trait by uniqueness at every finite place
where N is a unit. It does not extend a level at its own residue
characteristic.

The opens S_3 and S_11 cover S by gcd(3,11)=1, and intersect in S_33.
On S_33 the single integral 33-mark projects to the two integral
sections, by their uniqueness and the known generic 33-to-3/11 CRT
identities. The pullbacks of the two universal polarized surfaces are
therefore canonically isomorphic over S_33, through the actual
universal 33-surface. One must not glue just because the coarse
coordinates match; that step would leave an undetected twist.
The actual isomorphism over S_33 glues the pullbacks to an abelian
scheme 𝒜 over S with this O-action, identity and principal
polarization. Schemes and their morphisms glue over open covers;
properness, smoothness and geometrically connected fibers are local
on the base, as are the group law and polarization compatibilities.
Its generic identification is the exact selected A/L. This
argument is unaffected by a later common extension of L: pull
back the proper sections, rather than transporting unrelated
chosen models. No Néron base-change theorem at bad reduction is needed.

## The one rank-one Hodge lattice and its actual norms

Let H be the rank-one projective O_L module of sections of
det(e* Ω_{𝒜/S}), where e is the identity section. Its
localization at each w is precisely the Hodge determinant of the
same proper trait as in the finite KS construction: relative
differentials, pullback, and the determinant commute with the
actual base change of the smooth family. This good model is the
Néron model locally ([Conrad, Example 5.3, with BLR §1.2/8](https://math.stanford.edu/~conrad/papers/minimalmodel.pdf#page=13)). Therefore this is
the stable invariant differential lattice of A, without invoking
stable base change for a different model or imposing freeness on
the global determinant.

For the same nonzero arithmetic determinant frame H0 as in the
shared dt² construction put

    I = { a ∈ L : a H0 ∈ H }.

It is an invertible fractional ideal, and I_w=u_w O_{L,w} for a
local generator u_w ≠ 0. Define the norm of the *rational* frame
at w by r_w=|u_w|_w^(-1); the local primitive vector u_w H0 has norm
one. If n_w=ord_w(I), with the finite absolute value
|x|_w=(Nw)^(-ord_w x), then r_w=(Nw)^(n_w). This sign is important.
For example, in the larger lattice p^(-1) H0 the integral vector
H0 has norm smaller than one at p, not larger. Changing local
generator by a unit changes no r_w.

There are nonzero a,b in L with a O_L ⊆ I ⊆ b^(-1) O_L: take any
nonzero member of I for a; clear denominators of a finite set of
O_L-generators of I for b. For all places with both |a|=|b|=1 the
local inequalities |a|≤|u_w| and |b||u_w|≤1 give r_w=1. This proves
the exact adelic support from the two finite principal supports
without factoring I or choosing a global basis. Equivalently,
the localized inclusions give a=x_w u_w and b u_w=y_w with
x_w,y_w in O_{L,w}; the one source owner formalizes precisely
this argument and constructs the existing FrameNorms object.
It leaves the representability/gluing and the actual identification
of localized Hodge lattices classical, not hidden in a new arbitrary
height input.

## Match the real place weights and the exact stable height

At infinity put r_σ=||σ H0||_Yuan, the positive square root of
(2π)^(-2) times the absolute integral of σH0∧conj(σH0) on the
same abelian surface. This is exactly [Yuan v2 §1, §4.3](https://arxiv.org/html/2205.11334v2#S4.SS3)
and the already computed principal-period metric. Conjugate embeddings
give equal r_σ by complex conjugation of the algebraic differential
and absolute integral; summing over embeddings is therefore exactly
the existing InfinitePlace.mult weighting (1 real, 2 imaginary).
There is no second factor at complex places.

In this one arithmetic frame the metrized line's degree is

    -Σ_w n_w log(Nw) - Σ_σ log(r_σ).

At the finite places ord_w(H0 as section of H)=-n_w, which explains
the sign of the divisor term directly. For a nonzero integral
multiple of H0 it is equally the log of the index of its generated
submodule in H; the principal product formula makes the formula
valid in the given rational frame. Divide by [L:Q] to obtain
FrameNorms.normalizedDegree. Since this very line is the good
Néron Hodge line with the specified metric, the result is
h_Y(A), the stable height with Yuan's metric. Further finite base
change preserves it already on the good model: finite orders
multiply by ramification degrees and log(Nw) by residue degrees,
while each embedding is repeated [L':L] times. All terms and
the normalization multiply by [L':L]. Thus even a later common
height extension needed for the distinct modular Jacobian adds
no offset or new stabilization input to this A.

In dimension two the comparison h_Y=h_+=h_0+log(π) is the same
already pinned in the reviewed reverse integration. It follows from
the single square-metric ratio π^(-2) versus the measure with
2^(-2), not from doubling all places. Only after this degree equality
does the tensor square multiply the degree by two, via the existing
InducedLattice318.square_degree; the finite 210 in the inverse
section bound still occurs once.

This is a genuine classical production of one global model and its
adelic Hodge line for the exact selected A. It is not a native PEL
representability, proper section gluing, or Néron identification,
not a calculation of the separate modular Jacobian's line, and
does not change any reverse threshold. No local Lean verification.

Replay from this directory (the donor manifest paths are workspace-relative):

    sha256sum -c SHA256SUMS
    python3 check_hodge_lattice.py | cmp - EXACT-HODGE-LATTICE.json
