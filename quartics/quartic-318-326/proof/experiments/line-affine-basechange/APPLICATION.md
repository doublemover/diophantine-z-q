# Actual affine line modules and their original pullbacks

Three new applications use the pinned original baseline directly. There are
no producer copies in this packet. The original baseline already supplies
the canonical tilde/scalar-extension comparison in `TildePullback318`.
That source was read and reused, not claimed as a new missing theorem.

1. **Original input.** `LineSheafClass318.Line` has an actual module sheaf,
   a full covering family of original opens, and actual rank-one frames.
   `OriginalLineAffineModel318` consumes exactly these fields to obtain
   Mathlib local freeness and quasicoherence. No additional unverified
   rank-one presentation replaces the original sheaf.
2. **Full cover.** `ModuleFreeOpenFrames318.locallyFree` receives the whole
   original index type, the actual cover inequality and each original frame.
   The only conversion is the canonical one-element free-sheaf/unit iso.
3. **Actual affine module.** Over Spec R, `sections` is the genuine
   `moduleSpecΓFunctor` with its original structural R action. The comparison
   `canonicalIso` is the original tilde-Gamma counit `fromTildeΓ`.
4. **Module properties.** The exact prior `AffineLineFrameCover318.properties`
   yields finite presentation, flatness and rank one at every actual prime
   for that same section module. Its original principal-refinement and
   localization argument is retained, including full prime coverage.
5. **Prior canonical pullback.** `TildePullback318.pullbackIso` is built from
   the actual sheaf pullback/pushforward adjunction, actual affine direct-
   image section comparison, tilde-Gamma adjunction, and scalar extension/
   restriction adjunction. Its prior unit normalization is not replaced
   by an arbitrary abstract isomorphism. Any commutative ring map is allowed.
6. **New actual line comparison.** `sheafIso` runs from tilde of the actual
   extended section module through the inverse prior pullback comparison,
   then the actual pullback of the original counit, into the unchanged
   `LineSheafPullback318.line` object. `sheafIso_counit` records these exact
   factors. `sheafIso_naturality` proves agreement on every actual original
   module-sheaf morphism, not only on isomorphism classes.
7. **Actual global-section comparison.** `sectionsIso` and `sectionsEquiv`
   use the real tilde unit and the actual global-section image of that
   sheaf comparison. The endpoint is the original pulled line's module of
   sections. `sectionsIso_hom` fixes the two factors and their direction.
8. **Original contact consumer.** For any unit tuple c, the literal source
   normalization, original SourceOrder and its actual full affine chart
   embedding are retained. Scalar extension along any map out of this ring
   lands in the line pulled back along `Spec.map f` followed by that exact
   chart embedding. The original `LineClassPullbackLaws318.compositionIso`
   is the only composition comparison. No alternate source model, generic
   fiber or selected component is substituted.
9. **Boundary.** This packet supplies an affine bridge toward descent. It
   does not prove that overlap descent data is a coalgebra, that line
   objects descend effectively for fppf covers, or that the naive relative
   presheaf equals its associated sheaf. Degree zero, representability,
   Jacobians, norm duality, polarization and isogeny remain further work.
