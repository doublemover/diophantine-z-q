# Literal rational period chart readout, r2

Narrow repair of the two exact logged expressions in the first donor.
The function equalities read the original evaluations pointwise instead
of asking simp to turn an opaque Pi Add or Mul into a lambda. The pinned
pointwise differentiable sum/product lemmas are the to_fun versions
generated next to DifferentiableAt.add and DifferentiableAt.mul. The
checked coefficient math, statement, all other bytes and the two
unattempted consumers are unchanged. No local build.
