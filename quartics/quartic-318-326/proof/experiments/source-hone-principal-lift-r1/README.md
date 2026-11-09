# Principal parts lifted to the actual infinity and overlap rings

This is an uncompiled three-source closure: two exact pending principal-parts
predecessors and one new consumer. No local Lean run, recursive axiom audit or
independent acceptance is claimed. Hosted checking remains pending.

The new `ContactInfinityRegularFractions318` removes two concrete limitations of
the preceding field identity:

- `regularCoefficient P m` is an actual element of the original localized
  infinity base ring, constructed using its original inverse denominator. Its
  exact original-field image is P(u)/D(u)^m.
- `coefficient_fraction` proves that **every** element of that actual base ring
  has such a fraction representation, using the original localization property.
- `principalTerm R n` is an actual element of the original overlap ring, using
  the proved unit u and the original infinity-to-overlap map.
- `coefficient_principal_reduction` is an equality **inside that actual overlap
  ring**: each localized infinity-base coefficient times u^-n equals a bounded
  principal term plus the image of an actual infinity-ring element. Degree R<n
  is retained, including n=0.

The final equality is reflected through the already proved injective original
source-field embedding after using the exact original-field identity. Therefore
this is not merely an assertion that an abstract rational expression is regular.
Both the regular witness and the overlap principal representative are constructed
in the existing rings and passed through their existing maps.

No reduction of all eight root-monomial coefficients of an arbitrary overlap-ring
element is yet claimed. That requires assembling this scalar result with the
actual infinity basis and the original localization of its whole order at u.
Cancellation of the finite-chart image, five surviving H1 classes, independence,
spanning and compatibility with the five actual quotient pullbacks remain open.
The structural Q-module on H1 is also still separate.

Exact predecessor hashes are in COPY_BINDINGS.json. The original chart polynomial
compatibility, u-unit theorem, localization-surjectivity API and injective field
embedding are used without changing their sources or their normalization.
Unit coercions and field/section algebra instance alignment remain hosted Lean
elaboration risks. Nothing is admitted to the accepted progress snapshot here.
