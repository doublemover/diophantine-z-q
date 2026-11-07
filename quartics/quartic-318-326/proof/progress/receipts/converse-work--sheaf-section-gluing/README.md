# Genuine sheaf-of-modules section gluing

Three public theorems and one section constructor are checked in one module
(seven recursive declarations, including helpers). The target is Mathlib's
actual `SheafOfModules` over an actual sheaf of rings on a topological space.
The final pair belongs to `M.sections`, with naturality on all opens. No
parallel substitute for sections or a final gluing axiom is introduced.

`module_unique_gluing` invokes the actual sheaf condition over an open cover.
`fromTop` constructs the corresponding natural global module section, and
`global_unique_gluing` proves uniqueness in that genuine section type.
`pair_from_quadratic_frames` takes actual rank-one coordinate linear
equivalences on chart and overlap section modules, actual frame restriction
identities, and the quadratic coefficient transition already proved in the
overlap packet. It derives compatibility of the module sections, then uses
the sheaf property to produce the unique global pair.

The direction is fixed explicitly: the coefficient pair transforms by u²
when the dual derivation scales by u; the other frame restriction has the
inverse square. Their cancellation is proved. No compatibility conclusion for
module sections is supplied to the final theorem.

## Scope

An actual source scheme/stack, its actual bicanonical sheaf of modules, an open
cover, and the identifications of source affine coefficients with the local
frames must still be realized. This theorem does not assert the existence of
that source atlas or line bundle, or prove its invertibility from section
modules alone. For an already realized invertible sheaf it closes the
local-to-global mechanism using the actual sheaf API. Stack descent beyond
the supplied sheaf remains geometric.

Run `bash verify.sh`: Lean4.35.0, Mathlib
56a005855ea17e0b0958f73ec801ae140b0a1679, strict kernel checking and recursive
standard-axiom audit. The official sheaf-of-modules dependencies were obtained
from the project dependency cache. No repository, Git or frozen source changed.
