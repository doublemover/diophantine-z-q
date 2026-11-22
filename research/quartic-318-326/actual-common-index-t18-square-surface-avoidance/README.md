# The literal input-zero square-match surface and unconditional avoidance

These independently reviewed notes concern explicit sufficient square tests for one fixed scalar first point, not all possible points on the secant quartic.

- [Exact double cover](surface/COMMON-INDEX-T18-LITERAL-SQUARE-COVER.md): the orbit uses the two-dimensional restriction of scalars, with a genus-25 generic fixed-arm slice.
- [General type](general-type/COMMON-INDEX-T18-LITERAL-SQUARE-COVER-GENERAL-TYPE.md): the plus-sign cover remains of general type after resolving the boundary and torus singularities.
- [Unconditional avoidance](avoidance/COMMON-INDEX-T18-HILBERT-AVOIDANCE.md): there are arbitrarily large same-key Ready indices at which the two optional square matches fail and the complement is nonsquare.

None of these results identifies an index, gives a companion point, proves finiteness of matches, or decides the unrestricted secant equation. See the [signed independent review](cold/INDEPENDENT-T18-SQUARE-SURFACE-AND-AVOIDANCE-REVIEW.md).

```sh
sha256sum -c SHA256SUMS
for part in surface general-type avoidance cold; do
  (cd "$part" && sha256sum -c SHA256SUMS) || exit
done
```
