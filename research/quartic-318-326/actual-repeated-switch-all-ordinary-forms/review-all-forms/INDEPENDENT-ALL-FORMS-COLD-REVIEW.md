# Cold review of the final ordinary variation after repeated switches

Reviewed the actual all-forms theorem (ce822b9a… and 3977ec36…),
not merely the earlier one-pair argument. The following checks pass.

1. The old pure inertias, including the signed-p47 mark corrections,
   have support disjoint from all added pair primes and kill the
   old a-plane. The new recursive planes project to an invertible
   copy of that old plane when pair support is removed. The
   graph replacement at each pair has the same strict complement
   and retains the actual normalized F_*. Therefore the old
   three color spans and the old block quotient descend through
   each step and are literally unchanged. The odd-power order
   governor argument applies at the same good odd inertia primes.
2. On right-composing each recursive H_j with C_j⁻¹ the formula
   really telescopes. The character support of H_k is exactly
   contained in span(a,D_A,D_B); the two phase products have
   disjoint support, and both phases occur. At the last B-pair
   strict representative, the valuation first eliminates D_B.
   Its unit character then eliminates a, since the last prime
   sees every earlier pair product as a square. Removing the
   F_* coefficient leaves only the coordinate class
   (−1)^u D_A^v. The mark coordinate is independent of these
   generators (2399 in the first coordinate, odd p47 in the other
   two); hence the normalization is linear.
3. If this last coordinate were exactly −1, transporting back
   to the old quotient through the strict complements could
   multiply it only by positively supported a or pair products.
   The earlier exact 4de5369a coordinate computation applies on
   the old D_i: this is in the old B_i, hence changing by a
   representative of the old plane and/or mark can set the
   coordinate to 1. Their coordinates are positive; they cannot
   remove a negative sign. Thus pure −1 is excluded. The kernel
   of the map taking the remaining coordinate is the true final
   same-line space, which is zero by 6bce1645…. Its image therefore
   has dimension at most one.
4. The wedge span with the annihilator of an at-most-one-dimensional
   space is all alternating forms on that block; there is no
   missing diagonal condition in characteristic two. The mixed
   wedges independently reset the off-block entries. The last
   pair supplies the hyperbolic toggle by an inertia square,
   preserving all normalized mark rows and quadratic norm phases;
   the residue-coordinate exclusion only removes finitely many
   units. After that choice the wedge shifts fix the hyperbolic
   plane and mark pointwise and use the same fixed cap.

This proves the announced maximal ordinary rank 2+2 floor(dim Q/2)
within the actual repeated-family cap. Neither dimension parity,
odd rank, rationality, nor pointed higher compatibility follows
from this cold pass.

Signed: independent reviewing subagent, paper/source only.
