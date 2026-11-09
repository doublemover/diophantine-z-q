# Actual relative line-class pullback

Six new modules pass strict Lean 4.35.0 checks and a private-inclusive recursive
audit of **114 declarations**, using only `propext`, `Classical.choice` and
`Quot.sound`. The exact 471-module predecessor closure was reused from verified
artifacts of the 1,837-module snapshot. This is not a fresh predecessor rebuild,
hosted validation of the new packet, or independent source acceptance.

The construction proves that the actual pullback of original line sheaves
preserves tensor products. It then constructs the original group-valued
pullback, the quotient by actual base-line classes, and its contravariant
functor on actual scheme fiber products. All scheme tests are included; no
flatness, affineness, reducedness, or field-point restriction is imposed.

The final consumer instantiates this naive relative Picard presheaf on the
original contact normalization and all five original completed elliptic
quotient targets. Their original maps give actual pullback natural
transformations, with explicit original-line formulas after every base change.

This is **not a represented Picard or Jacobian scheme**. Fppf descent and
sheafification, the relevant size comparison, representability and degree-zero
component, arbitrary-base norm compatibility, polarization, and the isogeny
remain separate. The overall height and integer-witness obligations are
unchanged.

See `APPLICATION.md` for the nine-obligation source/consumer comparison,
`DEPENDENCIES.json` for the exact predecessor closure, and
`validation/receipt.json` for source-bound check evidence. The six source files
are outside the accepted progress manifest and await bounded non-author review
and a coordinated integration decision.
