# Actual even-contact base change and normalization

This packet proves the concrete local algebra joining the formal C2 quotient to the finite étale even-contact cover. All five modules pass strict Lean kernel checking; the exhaustive recursive audit checks 101 declarations and permits only propext, Classical.choice, and Quot.sound.

## Actual constructions

- `QuadraticPresentation318` identifies the actual quadratic algebra with the actual polynomial quotient `R[Z]/(Z²-b)`.
- `ContactBaseChange318.baseChange` computes the actual tensor product along an actual ring/algebra map sending the base parameter to `u*pi^(2m)`. `formalBaseChange` applies this to the distinct formal cover algebra with base map S↦T², rather than the identity formal-series algebra. The generator is tracked exactly.
- `contactMap` sends the raw root Z to `pi^m` times the root of the existing unit-root algebra `EvenContactEtale318.RootRing u`; it assumes no chosen square root.
- `ContactGenericFiber318` constructs the inverse when the parameter becomes a unit. `awayEquiv` is an actual isomorphism after localization at pi. `genericFiberEquiv_on_order` proves compatibility with the concrete contact map, not just an abstract existence of an isomorphism.
- `ContactOrder318` proves actual finiteness/freeness and injectivity of the raw contact map over a domain when pi is nonzero.
- `NormalizedContactOrder318` uses the independently proved smooth-base-change integral-closure theorem to prove the unit-root algebra is the actual integral closure of the concrete contact order in its generic fiber. The actual algebra action, scalar tower, order injection and compatible generic-fiber equivalence are constructed here. The DVR theorem `normalized_even_contact` proves that this normalization is finite étale over the DVR when 2 is a unit.

## Scope

The coefficient/domain/field/DVR hypotheses are the actual Mathlib structures. The algebraic normalization result is proved, not supplied as a normality or normalization premise. A possibly split quadratic algebra is never treated as a domain or assigned an unjustified fraction field.

What remains outside this packet is geometric realization: the actual completed source curve/model, its tame quotient coordinate, the actual base-change map from the formal parameter algebra, and the identification of this generic-fiber algebra with the source geometric cover. There is no assertion here of the global geometric realization required by the final Diophantine theorem.

## Replay

Run `bash run.sh` from any directory. It builds all five modules and the exhaustive audit with `debug.skipKernelTC=false`, using the pinned Lean/Mathlib installation and the frozen formal model, unit-root étale, and normalization dependencies. Generated `.olean`, `.ir`, exploratory logs and checks are not proof-source deliverables.
