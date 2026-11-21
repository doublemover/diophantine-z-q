# The actual filled compact curve and the same algebraic normalization

This is a paper comparison using the literal curves already constructed
in the project. It supplies the original point identification at omitted
elliptic values and cusps, without identifying the Jacobian with another
abelian variety, choosing another normal model, or invoking GAGA.

## Fixed actual inputs

Let Y be the actual complex manifold
AllCuspFilling318.Filled N hN, for the original level N≥5, with its
registered old and new charts. AllCuspComplexCurve318 and
AllCuspConnected318 provide that this very Y is compact, Hausdorff,
second countable and connected. The original fine quotient embeds in Y
by AllCuspFilling318.original, and its complement is the set of distinctly
embedded finite actual cusp ends. This is not an atlas constructed
anew in the present argument.

Let X be the original algebraic compact normalization of the literal
primitive field, with its selected coefficient embedding into C and
the resulting complex curve. It is finite over the actual projective
J-line, and we use as affine charts exactly the inverse images of the
finite J and reciprocal 1/J charts. In particular their affine rings
are finite over ℂ[J] and ℂ[1/J], respectively. These are the actual
two charts in the strict Compact70 output: the normal charts and their
structural morphisms, not ad hoc monogenic models at the branch fibres.
The normal complex curve is nonsingular: in dimension one a normal
local domain is a DVR, and the base complex field is perfect. Equivalently
the smooth same compact comparison may be supplied as the originally
chosen geometric compact curve. We use analytification of affine
complex equations and the local complex implicit function theorem for
smooth points, not a general analytification comparison theorem.

The original ordinary open U is the locus J not in {0,1728,∞}.
On its period side use the actual modular quotient and its actual
marked evaluation. The complex-root output identifies the whole
literal selected polynomial fibre with the marked abscissa values;
the rational readout gives a holomorphic family of those same
characters. The ordinary marked-point interpretation identifies two
periods with the same J and root exactly on one Γ1 orbit:
for fixed ordinary J the ordinary elliptic curve has automorphism
group {±1}, and on the actual short equation equality of abscissa
means the two marked ordinates are negatives of one another or agree.
Such marks determine the same isomorphism class, and the standard
lattice/level correspondence gives the orbit. Conversely equal
orbits have equal typed evaluations. Thus the actual comparison
on U is holomorphic and bijective, and is a biholomorphism of
Riemann surfaces. No numerical isolation of a chosen ordinary
root is used. The two subdomains below extend this particular map.

## One exact finite-ring extension argument

Let s belong to a punctured disk at one of the omitted points of Y.
On a small disk the actual base coordinate t(s) maps into one of
the two affine J-line charts and extends holomorphically to its
center. Write B for the corresponding literal complex normalization
ring on X; the punctured-sheet family is the actual character
ε_s:B→ℂ determined by the preceding ordinary map, with ε_s(t)=t(s).

For b in B choose its monic polynomial P_b(T) over ℂ[t], possible
because the algebra B is finite over ℂ[t]. It is enough, equivalently,
to use the characteristic polynomial of multiplication by b in any
finite free ℂ[t]-basis of B. Evaluating gives
P_b(T)|_{t=t(s)}(ε_s(b))=0. The coefficients stay bounded on a
small disk. The monic root bound therefore bounds ε_s(b) as s
approaches the puncture, and the removable singularity theorem
gives a holomorphic extension of this coordinate. The limits of
ε_s(b+b'), ε_s(bb'), ε_s(1) and of the scalar values preserve all
the ring laws and the complex algebra structure, so the filled
point is a character of B itself, with the same prescribed t-value.
This argument also works when the algebraic branch fibre is
nonreduced. It uses no reduction of B and does not identify
nilpotent scheme directions by comparing point sets.

Choose a finite set of generators of B over ℂ. Their extended
coordinate functions define a holomorphic map to an affine space.
The finitely many defining relations vanish off the puncture and
hence at its center, and the image is precisely in the same affine
complex chart of X. Replacing these generators does not change
the map, since its values on every b are fixed by limits.
This is the native prefix staged in SelectedActualNormalChartPunctureFill318,
using actual tensor fibre character, multiplication matrix and
pointwise algebra character APIs.

## Which disk and which side at each point

At a point above 0 or 1728 use the literal old chart of the
original fine quotient, lifted to the filled curve. It is a
complex coordinate even there: the action at N≥5 is free, so
there is no division by the coarse elliptic isotropy in this
source chart. The finite base coordinate is t=J; the only
omitted point in a sufficiently small disk is its center because
the actual quotient finite J-fibres are finite
(ActualJFinite318.finite_fiber). In particular the possibly
ramified base coordinate J−J(center) is not chosen as the source
parameter. Apply the preceding finite-ring extension.

At an actual cusp c use the registered AllCuspCharts318.newChart
and its coordinate q=q_w, with w the actual width
AllCuspQJ318.natWidth N hN c. This is the earlier constructed
horoball quotient coordinate exp(2πi γ_c^{-1}τ/w) and its filled
disk, with the cusp at q=0. The exact earlier j identity on
that original chart is J=G(q^w)/q^w, G(0)=1, with holomorphic G;
AllCuspJPole318.cusp_reciprocal_analytic and
cusp_reciprocal_order give the same reciprocal germ through
the center. Therefore on a small punctured disk every point
is ordinary and t=1/J extends as q^w/G(q^w) with value 0.
Apply the same finite-ring extension in the actual reciprocal
chart. This does not select an independent formal branch or
divide by the derivative of J. In particular w need not be 1.

## The extension is an isomorphism of these same complex curves

Choose the disks small enough that their exceptional centers are
the only omitted points. They glue with the original ordinary
map: on their punctured overlap values agree by construction,
and any further overlap agrees by continuity into the Hausdorff
target. This constructs a holomorphic map Y→X(ℂ) over the
original J. Its image is compact, hence closed; it contains
the ordinary open, which is dense in X(ℂ) because its complement
is finite and each point of a smooth complex curve has a disk
neighborhood. Thus the map is surjective.

For an omitted y of X(ℂ), choose disjoint small disk neighborhoods
of any finitely chosen distinct preimages. At such a preimage
the nonconstant holomorphic map has a positive local order in
genuine source and target parameters; local nonconstancy follows
from connectedness and the nonconstant ordinary map. For every
sufficiently close ordinary value y' the argument principle
gives at least that many preimages in each chosen disk, counted
with multiplicity. But y' has exactly one preimage, and that
preimage is regular on the ordinary isomorphism. Therefore each
y has only one preimage and its local order is one. The complex
inverse function theorem gives the inverse on each disk. This
proves the global biholomorphism of the actual filled curve and
the actual same algebraic normalization. It does not use a
pointwise comparison to infer equality of arbitrary schemes.

## Literal null sets and the original Abel sum

Let E be the ordered-product union of projections onto the actual
finite discarded set consisting of these two finite fibres and
the actual cusps. Under the proved point identification this is
the same removed set of the original algebraic compact curve.
In a product of registered original disks each forbidden
coordinate is in a finite set of chart values, including q=0
in its actual cusp disk and the fine source-chart value at an
elliptic point. Thus the checked Null3 product argument applies
to those literal subsets; no noncompact-period chart is used
at the missing cusp itself.

Use the actual Abel map to J_X from the same algebraic curve,
now composed with the proved comparison on the source. Shrink
each product patch so its image lies in an actual injective
logarithm chart of this same J_X. Its local lifted holomorphic
map sends the discarded coordinate subset to a Lebesgue-null
set; the same unnormalized lattice volume in that target
chart assigns its true image measure zero on **all** subsets,
not just Borel ones. Critical images use the separate native
Jacobian argument. The exact ordered patch filtration of the
previous same-atlas null paper then yields the genuine discarded
and critical sets used in the Abel volume calculation.

This paper does not supply the full native complex-point manifold
of the algebraic scheme, native analytification or native Abel
sum. The cusp/old atlas and the compact algebraic two charts
are exact original source inputs; the finite extension and
comparison are paper reasoning with the indicated staged native
prefix. It makes no claim that the chosen arithmetic point is
regular, and no claim of a compiled global height.
