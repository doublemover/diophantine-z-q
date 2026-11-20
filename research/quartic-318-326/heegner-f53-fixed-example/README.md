# A fixed Heegner example for the original 318/326 route

This is a reproducible **one-input arithmetic check**, not a universal rank theorem or a native quartic proof. It uses the literal curve
`E_323: y^2 = x(x-323)(x+969)`, the ordered local mark `(17,1)`,
and the auxiliary CM field `Q(sqrt(-455))`. The analytic example chooses a based modular parametrization at level 5,007,792; no claim is made that this parametrization was already selected in an unrelated proof.

- The exact 20-class signed trace has 5,760 retained summands over `F_53^2` (including repetitions). Its actual reduction is `(1,25)` on `E_323(F_53)`, with order-13 projection `[224](1,25)=(42,42)`. The trace nontorsion deduction uses good reduction at 5, where `#E(F_5)=4` and `#E(F_25)=32`.
- The companion central value for `E_{-146965}` is nonzero, and the exact original-base primitive-period normalization at `h_*=-455` is `2048=2^11`. This is an auxiliary even reference, not the later joint-address family.
- The explicit rational affine point in the proof note is a separate check of the original mark. Its agreement with the trace modulo 53 does not identify the two points over Q. The separate squareclass check shows that this `beta=17` example cannot be any literal pole of the current prepared producer.

## Quick verification

Run from this directory with Python 3.12+ and only its standard library:

```sh
sha256sum -c SHA256SUMS
python independent-review-nov20/f53-full-oriented-trace-rendered-r1/check_full_trace_independent.py
python high-hom-1120/heegner-odd-residue-example/certify_exact_even_period.py
python joined-work-20261120/rc-d1-323-pointpair-r1/check_exact_point.py
```

The independent checker recomputes all 5,760 signed group additions, the 416 genuine low-chart keys, the common Gauss phase, and the final order-13 projection, without importing the producer. The primitive-period checker uses the included prior exact L-value interval.

## Regenerate the calculations

```sh
export PYTHONDONTWRITEBYTECODE=1
work="$(mktemp -d)"
trace=high-hom-1120/heegner-f53-descended
even=high-hom-1120/heegner-odd-residue-example

python "$trace/actual_20_class_trace.py" --jobs 4 > "$work/trace.json"
cmp "$work/trace.json" "$trace/ACTUAL-FULL-TRACE-F53.json"
python "$trace/finalize_exact_trace_phase.py" "$work/trace.json" > "$work/phase.json"
cmp "$work/phase.json" "$trace/EXACT-FINAL-TRACE-F53.json"

c++ -std=c++20 -O3 "$even/fixed48_theta_ntt.cpp" -o "$work/f48"
"$work/f48" 4000000 > "$work/coefficients"
sha256sum "$work/coefficients"
python "$even/certify_companion_value.py" "$work/coefficients" 5 7 13 17 19 > "$work/even.json"
cmp "$work/even.json" "$even/COMPANION-CENTRAL-INTERVAL.json"
python "$even/certify_exact_even_period.py" > "$work/period.json"
cmp "$work/period.json" "$even/EXACT-EVEN-PERIOD-455.json"
```

The 4,000,000 coefficient stream is generated, not vendored; expected SHA-256:
`87f403dccccbd1e56ae5bbcfac6690c8f8dcd06db26de65c6187a0734dbde01e`.
The directory levels keep the independently reviewed scripts and their relative imports byte-for-byte.

## Mathematics and boundaries

- [Actual finite trace, CM orientation, and nontorsion](high-hom-1120/heegner-f53-descended/ACTUAL-FULL-TRACE-HEEGNER-323-F53.md)
- [Actual marked level structure and low map](high-hom-1120/heegner-f53-oriented/LITERAL-F53-ORIENTED-PROJECTION.md)
- [One complete signed branch and exact descended endomorphism](high-hom-1120/heegner-f53-descended/FIRST-ACTUAL-FULL-TRANSLATE.md)
- [Exact even primitive period and lattice](high-hom-1120/heegner-odd-residue-example/EXACT-EVEN-CENTRAL-LATTICE-455.md)
- [Exact marked point pair and prepared-pole scope](joined-work-20261120/rc-d1-323-pointpair-r1/POINTPAIR-AND-PREPARED-SCOPE.md)
- [Uniform scalar squareclass exclusion](joined-work-20261120/rc-d1-323-pointpair-r1/SCALAR-NONSQUARE.md)
- [Independent full finite replay and Fricke audit](independent-review-nov20/f53-full-oriented-trace-rendered-r1/EXACT-F53-FULL-TRACE-COLD-REVIEW.md)

The link from the algorithm to the Heegner values uses the classical oriented CM specialization/ideal action, the actual modular quotient and Gauss twist, and prime-to-53 reduction compatibilities as stated in those notes. The arithmetic scripts do not formalize those theorems. The fixed example does not fill the analytic supplier for all selected inputs.

See also the [independent primitive-period normalization review](independent-review-nov20/even-central-455/EXACT-EVEN-PRIMITIVE-PERIOD-COLD-REVIEW.md).
