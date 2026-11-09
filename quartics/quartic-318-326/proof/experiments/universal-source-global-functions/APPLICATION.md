# Universal original structure pushforward and all-test rigidification

Five new sources use twenty-one unchanged producer copies to close imports
against the pinned original 1,837-source baseline. Copies are not additional
results; source acceptance is separate from compiler evidence.

1. **Genuine pinned base-change theorem.** `FlatGlobalSections318` invokes
   the actual `isIso_pushoutSection_of_isQuasiSeparated_of_flat_right`
   theorem in pinned Mathlib's `Morphisms/Flat.lean`. Its finite affine-cover
   equalizer proof is not replaced by an assumed cohomological base-change
   statement. Properness supplies the actual source's compactness and
   quasi-separatedness.
2. **Canonical pushout.** The actual structural global-section maps form
   the original pushout square for any flat affine test over the affine
   base. If the original structural map is an isomorphism, pushout stability
   proves the actual new structural map is an isomorphism.
3. **Full inverse-image opens.** On an arbitrary test scheme, the same
   theorem is applied to every affine open of the test and its full original
   inverse image in the source fiber product. No overlap or component is
   discarded. The map is the actual scheme `app`, not a chosen ring map.
4. **Actual structure sheaf.** `structureMorphism` is the original scheme
   structure-sheaf morphism into the actual sheaf direct image. The real
   affine-open basis and the genuine sheaf isomorphism criterion prove this
   morphism is an isomorphism. Consequently every open component is an
   isomorphism, including nonaffine and nonquasicompact opens.
5. **Original contact source.** The unchanged original structural Q-global-
   constant theorem proves the actual original `p.appTop` is an isomorphism.
   The actual original normalization and structure map are retained.
   Every scheme morphism to Spec Q is flat, discharging the generic premise.
6. **Universal consumer.** For every scheme T over Q, the actual structure
   morphism `O_T -> (p_T)_* O_(X_T)` is an isomorphism, with exact original
   all-open app maps. There is no reducedness, field, affine, or quasicompact
   assumption on T. This is a structure-sheaf statement, not only a statement
   about geometric fibers or global sections on fields.
7. **Actual section evaluation.** For an actual section, its identity after
   the structural map makes its actual global-section evaluation inverse
   to the structural isomorphism. The same conclusion holds for the actual
   pulled-back section on every flat test.
8. **All-test rigidified classes.** The exact previously constructed contact
   field family and section satisfy these premises. On every further scheme
   test, every original relative class has an actual rigidified line
   representative, and two such objects have equal classes exactly when
   one and only one actual compatible module-sheaf isomorphism exists.
   This covers all actual lines, not only lines pulled back from Q.
9. **Boundary.** The last classification concerns the original quotient by
   base lines, not an asserted identification with all associated fppf sheaf
   values. Effective fppf object descent is not proved here. Degree zero,
   representability, a Jacobian, norm, polarization and isogeny remain further
   work. No Q-rational point of the original source is assumed.
