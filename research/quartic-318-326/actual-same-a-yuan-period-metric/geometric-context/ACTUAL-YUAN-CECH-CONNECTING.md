# The same family's connecting map before taking determinants

This narrow step concerns the actual connecting map in Yuan §1 for
the given literal D=210 fine universal family A -> X. It is independent
of the modular Jacobian computation on X_1(M). Fix an affine
neighborhood of the actual ordinary characteristic-zero fine point.
For the separated abelian scheme over that affine base choose a
finite affine cover. Its intersections are affine: separated over
an affine base gives affine diagonal. For quasi-coherent sheaves the
resulting Čech complex computes cohomology
([Stacks Project, Lemmas 30.2.5–6](https://stacks.math.columbia.edu/tag/01XD)).

Use the short exact sequence of that very family

    0 -> pi* Omega_X -> Omega_A -> Omega_{A/X} -> 0,

the exact one in [Yuan §1](https://arxiv.org/pdf/2205.11334#page=3).
At the smooth ordinary point the right-hand sheaf is locally free,
as is the left-hand one; the sequence is locally split as a sequence
of modules. The map along the marked point is the restriction of this
sequence as vector bundles; it is NOT the sequence recomputed for
the constant A/Spec L, which would omit the original relative
cotangent direction. Choosing an affine cover on the base chart
or restricting a common affine refinement of the two pulled-back
families gives the same current family and exact cochain squares.
On each affine in the common cover the short sequence of
quasi-coherent modules remains exact on sections. This holds for
the chosen ordinary generic comparison; it supplies no new
integral good-reduction assertion on the bad special fibers.

In a fixed degree-zero lift b of a global relative form s, the
Čech difference d_E(b) maps to zero in the degree-one relative
column since s is global. It therefore equals i_1(a) for a unique
cochain a of the left column. The connecting class is [a].
A second b' differs from b by the image of a left zero-cochain
since both lift s. Its effect on a is the coboundary of that
left zero-cochain and nothing more. In degree two the differentiated
a is zero by injectivity and d^2=0. Thus the class is in the actual
cohomology subgroup of the ambient degree-one quotient, not a
claim that the entire cokernel is H^1. This defines the canonical
connecting map and proves its linearity without postulating it.

After applying a comparison of exact cotangent sequences, the
image of b is a lift of the image of the same s and the image
of a is the exact corresponding difference. This is the
naturality theorem in the source and works for cover refinement
and compatible coefficient restriction. For the characteristic-zero
level-33 overlap the individual exact cotangent sequences pull
back because the relative base maps are étale. The family
base changes, order action and chosen polarization identify the
two sequences with the same ones. The identified map over the
actual marked ordinary cotangent V is thus the same phi0 before
applying Yuan's projection formula, H^1(O_A)=Lie(A-dual), its
polarization, and the already verified ordered determinant map.

The source operates on the actual first terms and squares of such
a supplied Čech presentation, not on a supplied connecting
map or a field-point scalar equality. It does not formalize the
scheme cohomology comparison, the source of affine covers for
that universal PEL family, its Hodge/Picard comparison, or
Yuan's integral image theorem. Those are real classical inputs.
The explicit native theorem for the cocycle, the map modulo
coboundaries and the cochain naturality have independent finite
arithmetic controls and are a standalone candidate for hosted
checking on the pinned mathlib. No local Lean or remote writes.

    sha256sum -c SHA256SUMS
    python3 check_cech_boundary.py | cmp - EXACT-CECH-BOUNDARY.json
