# Independent actual Jacobian and localized Kähler-frame review

Accepted. Four frozen sources were copied byte-for-byte and independently read/rebuilt with strict kernel checking. An exhaustive recursive audit passed111 declarations across four modules, using only standard axioms. No originals were edited.

The actual localization presentation adds its genuine inverse variable and equation, so the composed Jacobian is a product of units. The one complementary coordinate is correctly the unselected Fin2 coordinate. Mathlib's actual submersive-presentation theorem gives its differential as a one-element basis. The coefficient frame is normalized on that exact differential, and generation is deduced from the basis rather than assumed.

The three source specializations correctly use dx on the finite F_y chart, dy on the finite F_x chart, and dx on the infinity F_z chart. The resulting derivations are the dual universal relative derivations on these actual rings. No discriminant or basis oracle is substituted for the local construction.

The localization packet uses the actual formally-etale Kähler tensor equivalence in the correct direction, then base-changes the actual frame and contracts T⊗S S to T. Its mapped-differential identity is exact. Formal étaleness for a localization is supplied by the actual localization instance. Normalized differentials remain normalized and generate the target module. Prime-local instances and derivation compatibility use the same actual chart frames, not new independent choices.

Retained boundary: these are RELATIVE FAMILY differentials Ω(chart/base). They are not the compact modular base curve's canonical differential line. Actual Scheme-stalk transport, source-curve/coordinate realization and global sheaf/canonical-line interpretation remain distinct. No DVR, regularity of an arbitrary prime localization or global frame is silently asserted. Imported submersive-presentation and Kähler/localization theorems are used as checked Mathlib dependencies. No mismatch was found.
