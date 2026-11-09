# Associated fppf line-class sheaf

This continuation adds three sources to the six unchanged, independently reviewed
sources preserved at `2d147d358d23bba634a7daf34fcdc7fc9d5a4d33`. The copies of
those six sources are byte-identical and included only to make this experiment
dependency-closed against the unchanged 1,837-module baseline. They are not six
new results. The compilation/audit receipt and any non-author acceptance are
separate evidence. No manuscript passage or accepted progress manifest changes.

1. **Inputs and universe.** The same arbitrary schemes and original structure
   map `p : X → S` are used. The site is all `S`-schemes in universe `u`; the
   group presheaf is valued in `CommGrpCat.{u+1}`, exactly as constructed in the
   preceding packet. It includes arbitrary nonaffine and nonreduced tests.
2. **Topology.** `topology S` is literally `Scheme.fppfTopology.over S`.
   The underlying fppf precoverage consists of jointly surjective, flat,
   locally finitely presented scheme maps. The over-site cover criterion is
   the original `GrothendieckTopology.over` criterion. No Zariski or field-point
   topology is substituted. Subcanonicity is inherited from the proved original
   fppf topology and its proved over-site construction.
3. **Existence rather than an assumption.** The new `coverColimits` instance
   constructs the required colimits using
   `CommGrpCat.FilteredColimits.colimitCocone` and its actual universal-property
   proof. Their universes are explicitly fixed. Original concrete limits,
   filtered-colimit preservation, and the cover-size instance then supply
   `HasSheafify` through Mathlib's proved left-exact sheafification theorem.
   The caller supplies no `HasSheafify`, representability, or descent premise.
4. **Exact object.** `sheaf p` is the associated group sheaf of the unchanged
   `RelativeLineClassBaseChange318.presheaf p`. Its `isSheaf` theorem is the
   actual sheaf property. `unit p` is the actual adjunction unit, not a chosen
   map to an unrelated sheaf.
5. **Universal property.** `lift`, `unit_lift`, and `lift_unique` use the same
   sheafification adjunction. Every natural map from the original relative
   presheaf to any fppf group sheaf factors uniquely through this exact object.
   No proof that the naive presheaf was already a sheaf is smuggled in.
6. **Local interpretation.** The canonical unit is proved both locally
   surjective and locally injective. The actual two original quotient maps are
   surjective, so its local image can be described by genuine original line
   sheaves on the actual full fiber products. `local_original_line_iff` gives
   that exact representative criterion. `local_original_lines_cover` proves
   the image sieve is fppf covering. `local_equality_cover` proves equality in
   the sheaf is detected by equality of naive relative classes on an fppf
   cover. It does not claim a global line representative.
7. **Map directions and scalar data.** Sheafification extends the original
   pullback natural transformation from the target relative presheaf to the
   source relative presheaf. `unit_pullback` proves the full unchanged-input
   square, and `pullback_unique` characterizes the extension. These are Picard
   pullbacks. They are not the opposite-direction norm maps or the curve
   differential pullbacks used by a future Jacobian norm cotangent argument.
8. **Actual consumers.** `ContactFppfLineSheaf318` uses the same rational
   structure maps and all five original completed quotient maps from
   `ContactRelativeLinePresheaf318`. It constructs their actual sheaf
   morphisms, original-presheaf unit squares, and uniqueness statements. The
   source is the original contact normalization, with no selected component,
   replacement isogenous variety, or assumed rational section.
9. **What is not established.** This is an actual fppf group sheaf, but not a
   representing scheme or algebraic space. It does not construct a degree map,
   degree-zero component, Jacobian, Poincare bundle, polarization, norm under
   arbitrary base change, or isogeny. Effective descent for chosen line objects
   and their isomorphisms is distinct from the general associated-sheaf local
   interpretation. The library comparison in `NEXT-PREREQUISITES.md` describes
   the next concrete work without turning unavailable theorems into premises.
