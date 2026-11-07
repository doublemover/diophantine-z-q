# Actual even-contact étale cover

Status: strict kernel replay and exhaustive project-module axiom audit passed: 32 declarations in two modules, 15 public theorems. Only `propext`, `Classical.choice`, and `Quot.sound` occur as axiom roots.

For an actual commutative ring R, a unit u, and invertible 2, this packet constructs the actual quadratic root algebra R[X]/(X²-u). Its distinguished root is a unit; the actual derivative 2X is a unit in the quotient. An explicit equivalence with Mathlib's standard-étale presentation proves that the algebra is étale. Its monic polynomial gives an actual rank-two free module, finiteness, and faithful flatness over a nontrivial base. Taking actual spectra gives a finite étale, flat, surjective morphism.

The algebra contains the explicit root X·π^k of the even contact u·π^(2k). Every field-valued root y with nonzero image of π factors through this algebra by sending X to y/π^k. The corresponding actual Spec map is proved to be over the base scheme. This last assertion concerns generic field-valued points, not arbitrary roots on a nonreduced special fiber.

## Source application and remaining boundary

This supplies the finite étale root cover used after an actual local branch equation is identified with z²=w and an even contact with u·π^(2k). Neither a square-root-existence premise nor an étale-algebra premise is supplied to the result. It complements `even-contact-hensel`, which constructs roots inside the actual Henselian ring under residue hypotheses.

The actual geometric local coordinate identification, the original DVR or strict henselization, the relation of this cover to a geometric normalization, and global model/field realization are not constructed here. No full geometric realization or FiveContact49Height is asserted.

## Rebuild

Run `bash build.sh`. Every compilation uses `-Ddebug.skipKernelTC=false`. Imported dependency oleans are reused. The exact unchanged official Mathlib StandardEtale source was strictly compiled locally because that olean was absent from the cache; the script repeats this step only if needed. No Mathlib source was modified.
