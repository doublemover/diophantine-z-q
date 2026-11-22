# Fixed-conductor 241: oriented prime exponents and binary ideal recovery

These two separately checked notes give the good-prime intersection formula and the exceptional-prime exclusion for the real CM-supported inert-29 receiver. The literal target still has moving fundamental discriminant. The construction requires the compatible new original mod-5 refinement and the independently pinned calibration over Q(sqrt(5),sqrt(6)); it does not change the original pole equation or assert the mod-5 guard for every previously frozen source index.

The first note retains the dual 241-line, the normalized Lie and exact level-48 flag, and the globally coherent determinant sign. The second excludes exceptional prime contributions under the stated inputs, then recovers the cubic class from four oriented imaginary quadratic ideals. No actual moving prime exponent, ideal, cubic phase, odd rank or marked rational point is supplied. The separate maximal-order saturation algorithm is not part of this packet.

```sh
sha256sum -c SHA256SUMS
(cd good-primes && sha256sum -c SHA256SUMS)
(cd exceptions-and-binary && sha256sum -c SHA256SUMS && python3 check_fixed241_exception_rows.py | cmp - EXACT-FIXED241-EXCEPTION-ROWS.json)
(cd independent-review && sha256sum -c SHA256SUMS)
```
