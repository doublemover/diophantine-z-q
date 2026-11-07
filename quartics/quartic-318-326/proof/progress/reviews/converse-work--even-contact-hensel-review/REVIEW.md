# Independent review: actual even-contact Hensel lifting

## Finding

The seven public results in `EvenContactHensel318.lean` match their declared
scope. No mathematical or source-interface mismatch was found. The proof uses
actual Henselian local rings, actual residue fields, separable closedness, and
the canonical DVR additive valuation. It does not assume the desired square
root or a unit/uniformizer decomposition.

## Checked chain

- For a unit, a residue square root is nonzero. A residue lift therefore has
  unit derivative `2a` when the residue characteristic is not two. The actual
  monic polynomial `X²−u` satisfies Mathlib's Hensel hypotheses, giving a root
  in the ring. Its unit property follows from its square being a unit.
- Separable closedness supplies a residue square root because the exponent two
  is invertible. This is the relevant separability condition, not an implicit
  algebraically closed residue-field assumption.
- The actual DVR theorem writes a nonzero element as a unit times a power of
  an irreducible uniformizer. Equality of its canonical value to `2k` forces
  exactly that exponent. The zero branch is separate, and exponent zero is
  included. The converse square criterion derives the even value from the
  multiplicative law for the canonical additive valuation.
- In any receiving field, equality of squares gives the two possibilities
  `y=f(z)` and `y=-f(z)`. Thus every root of the quadratic equation belongs to
  the image of the ring, rather than merely one selected root. This is an
  algebraic all-root statement, not a construction of an entire curve fiber.

## Exact application boundary

The strict henselization/unramified local ring, identification of the actual
completed tame quotient with `w=z²`, and descent of its finite coordinates to
an actual finite unramified extension remain separate inputs. The report and
theorem names retain these boundaries. The theorem alone does not identify
the geometric fiber with a quadratic algebra, or construct its fine-level
lift. The reciprocal coordinate at infinity can use the same algebra once
its actual local equation has been identified.

## Independent replay

The mathematical module and recursive audit were copied without modification
into `replay/`. `verify.sh` first strictly rebuilds the unchanged official
Mathlib Henselian source in an isolated overlay, then rebuilds the copied
module and its audit with `debug.skipKernelTC=false`. The overlay uses links
to the other pinned Mathlib artifacts and is recreated by the script; it is
not a vendor copy or a new mathematical dependency. The final comparisons
verify that the reviewed mathematical sources still equal the frozen originals.

Lean is 4.35.0 and Mathlib revision is
56a005855ea17e0b0958f73ec801ae140b0a1679. All ten declarations pass the recursive
standard-axiom check. No original packet, repository file, or Git state was
changed.
