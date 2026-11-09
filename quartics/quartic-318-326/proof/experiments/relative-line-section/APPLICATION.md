# Actual section normalization and rigidified line representatives

This packet adds four sources. Eight unchanged producer sources are copied
only to close the imports against the pinned 1,837-module baseline: four
relative-line sources, three field-point sources, and the exact frozen
`ContactFieldSection318` source. Copies are not new results. Compiler/audit
evidence and independent source acceptance remain separate.

1. **Original objects.** `Class X` is the quotient of original locally framed
   module sheaves by actual sheaf isomorphism. `RelativeClass p` is its quotient
   by the image of the original base pullback. Neither is replaced by a group
   defined only to have the desired equivalence.
2. **Actual section input.** The generic construction requires an actual
   scheme map `e : S → X` and the exact identity `e ≫ p = id`. It does not
   assume the rational source has a rational point. Pullback composition and
   identity prove `e* p* = id` on the original line classes.
3. **Explicit normalization.** The map sends `c` to
   `c * (p*(e*c))⁻¹`. Its homomorphism laws, trivial restriction at the section,
   annihilation of base lines, and fixed-point law on the section kernel are
   all proved. No degree map or numerical degree condition enters.
4. **Exact two-sided equivalence.** `quotientToKernel` descends that original
   map through the actual base-line subgroup. Its inverse is the original
   quotient map restricted to the original section-pullback kernel. Both
   composites are proved to be identity. This is the whole relative group,
   not its degree-zero subgroup.
5. **Actual rigidified objects.** `RigidifiedLine e` contains an original line
   and an actual module-sheaf isomorphism from its restriction to the original
   structure sheaf on the section. `normalizedLine` uses the original tensor,
   inverse and twice-pulled-back line objects. The proved faithful class
   equality supplies a genuine trivialization by classical choice; no
   effectiveness-of-descent premise is inserted.
6. **Coverage by original objects.** `kernelClass_surjective` and
   `relativeClass_surjective` prove that all classes have actual rigidified
   line representatives. `normalization_same_relative_class` compares this
   representative to the unchanged original quotient map. This does not
   classify rigidified morphisms or assert uniqueness of a trivialization.
7. **Full base changes.** `sectionOn` is the actual universal-property lift
   into the full scheme fiber product. Both projections and naturality with
   the original `totalMap` are proved. The equivalence and rigidified
   representative statements apply to every further scheme test, including
   nonaffine and nonreduced ones, without an added flatness condition.
8. **Actual source consumer.** `ContactFieldRigidification318` uses the exact
   original contact model, original structure map, explicit point field and
   original point-section from the frozen height producer. That field map is
   an actual finite etale fppf cover; `actual_cover` cites its original covering
   sieve. The construction works for every rational parameter and original
   unit tuple. Specializing the tuple to the published source units yields
   the same source structure map used by the fppf Picard packet, by definition.
9. **Boundary.** This removes the base-line ambiguity after the explicit
   section-giving cover. It does not provide a degree-zero component,
   representability, effective descent of rigidified objects and morphisms,
   uniqueness of rigidified automorphisms, a Poincare bundle, a Jacobian,
   polarization or isogeny. The required original structure-sheaf pushforward
   and geometric-fiber degree comparisons are not assumed.
