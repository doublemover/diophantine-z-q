# One exact norm equation for the named conductor-15 tests

For the literal original scalar or the specified denominator-cleared
retune, admitting the chosen lift and the chosen opposite Selmer class
is equivalent to a single displayed rational norm equation in a fixed
biquadratic field. The right-hand side uses the actual folded scalar
and the four known support factors directly. No complete factorization
or count of further primes is needed to state or verify a certificate.

A norm solution would exclude the constant-15 marked construction on
the retuned scalar, by its known nontrivial second pairing. For the
unchanged scalar the separate crossed sign is still needed. No norm
solution, rank, or rational point is asserted here; failure of the norm
does not exclude a different lift or the original PointPair.

- [Proof and exact norm equation](rc-native-helper-20261120/ct-original-constant15-single-admission-norm-r1/SINGLE-FIXED-FIELD-ADMISSION-NORM.md)
- [Signed independent review](independent-review-nov20/rc-constant15-single-admission-norm-cold-r1/INDEPENDENT-CONSTANT15-SINGLE-ADMISSION-NORM-REVIEW.md)

```sh
sha256sum -c SHA256SUMS
(cd rc-native-helper-20261120/ct-original-constant15-single-admission-norm-r1 &&
 python3 -B replay_fixed_admission_field.py | cmp - EXACT-ADMISSION-FIELD-CONTROLS.json)
```
