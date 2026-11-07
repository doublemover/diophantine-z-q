# Actual Kähler frames produce the source derivations

Thirteen public theorems and three constructed maps pass strict kernel
checking in two modules (35 declarations including generated helpers).
The starting objects are actual Mathlib Kähler differential modules and linear
frames, not an arbitrary differentiation operation with an assumed estimate.

`frameDerivation` uses the actual universal equivalence between module maps
from Kähler differentials and relative derivations. A shared normalized frame
generator forces compatibility on every differential. Hence the actual field
derivation agrees with the integral frame derivation on the local ring, and
integral preservation is derived. Actual differential generation
span{dz}=top implies that its coefficient in the integral frame is a unit.

Any generic rank-one frame can be normalized on a nonzero image of the
integral frame generator. This constructs a compatible field derivation rather
than assuming one. The source wrappers then derive both literal J²-scaled
vertical coefficients and the regular/unit-twisted horizontal coefficients,
including a unit coefficient horizontally. No field derivation, derivative
valuation bound, integral-preservation conclusion or Dz-unit conclusion is
supplied to these source wrappers.

## Precise remaining geometry

Actual integral and generic rank-one Kähler frames, the nonzero image of the
integral frame generator under the actual differential map, and source
coordinate/model data remain inputs. The packet does not prove a general
localization theorem for Kähler differentials. The normalized generic frame
is local to the selected integral frame; it does not silently identify
independently normalized derivations on different charts. The fixed-frame
compatibility theorems and preceding actual overlap-transition packet retain
that separate identification. Realization of the bicanonical line bundle,
source affine atlas, sheaf and stack is not asserted.

Run `bash verify.sh`. Lean4.35.0, pinned Mathlib
56a005855ea17e0b0958f73ec801ae140b0a1679, debug.skipKernelTC=false, recursive
standard-axiom audit. No repository/Git or frozen dependency changed.
