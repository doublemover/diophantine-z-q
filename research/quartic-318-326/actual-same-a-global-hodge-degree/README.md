# The stable Hodge degree of the original selected surface

The [proof](global-hodge/ONE-GLOBAL-HODGE-LINE-OF-THE-ACTUAL-SELECTED-SURFACE.md)
globalizes the actual marked local models of the selected D=210 surface
in the reverse of quartics 318/326. The integral 33-mark over the common
open, not only the coarse point, identifies the actual 3- and 11-level
models. Thus they give one abelian scheme over the same height number
field's ring of integers. The proof computes the adelic lattice norm,
the exact stable-degree normalization, and its behavior under extensions
of that same field. There is no statement about the distinct modular
Jacobian, a new threshold or the forward direction.

The [exact fine overlap](level-overlap/THE-SAME-POINT-FINE-OVERLAP.md)
and [independent cold review](reviews/INDEPENDENT-SELECTED-GLOBAL-HODGE-LINE-REVIEW.md)
are included. The proof uses the classical actual fine PEL models,
valuative criterion, and good-model Néron theorem, not a native
construction of those objects.

Replay with Python 3 standard library:

    sha256sum -c SHA256SUMS
    python3 global-hodge/check_hodge_lattice.py | cmp - global-hodge/EXACT-HODGE-LATTICE.json
    python3 level-overlap/check_original_fine_overlap.py | cmp - level-overlap/EXACT-FINE-OVERLAP-CONTROLS.json

The examples check lattice norms (including a nonprincipal ideal)
and extension weights, not numerically compute a stable height.
