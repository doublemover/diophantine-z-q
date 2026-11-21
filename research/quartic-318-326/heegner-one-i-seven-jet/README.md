# Exact marked-cover search by p-adic jets

This source package keeps one fixed actual one-I parameter
`d = 2811626664334219040035976315`, with `q = 119851`, and the same
marked relative cover throughout. It includes the exact local Selmer
and tangent inputs, globally minimal model, Cremona–Fisher–Stoll
reduction, dual-plane search, higher-jet auxiliary-quadrics search,
and the independent complete seven-jet replay.

**Result.** The final run checks all 3,776 auxiliary quadric sections
over the rationals and finds no rational point in their union. Its
exact coverage includes every primitive integer vector of sup height
at most 949,470 in the reduced projective model. This is a finite
search certificate, not a global height bound, a rank result, a
point on the marked curve, or a result on its companion curve.

Read the [final algorithm and proof](actual-one-I-seven-jet-quadrics-r1/SEVEN-FORMAL-COEFFICIENTS-AUXILIARY-QUADRICS.md),
the [original marked back-map](actual-one-I-third-cover-reduced-r1/EXACT-REDUCED-MARKED-POINT-SEARCH.md),
or the [independent receipt](independent-review/INDEPENDENT-SEVEN-JET-REVIEW.md).
The original hashed files are unchanged. Bibliographic clarification:
the description of the p-adic Elkies–Heath-Brown search is at the
**end of §6.1** in [Fisher, arXiv:0711.3774](https://arxiv.org/pdf/0711.3774),
p. 25; §6.2 begins the flex-matrix construction.

## Replay

Run from this directory with Python 3 and SymPy 1.14. The parallel
flag only schedules independent bins and does not change the output.

```sh
sha256sum -c SHA256SUMS
for d in actual-* independent-review; do (cd "$d" && sha256sum -c SHA256SUMS); done
(
  cd actual-one-I-split-isogeny-selmer-r1
  python3 -B check_isogenous_exact_selmer.py | cmp - EXACT-ISOGENOUS-SEL2.json
  python3 -B check_actual_minimal_intersection.py | cmp - EXACT-MINIMAL-INTERSECTION.json
)
(
  cd actual-one-I-explicit-third-isogeny-cover-r1
  python3 -B check_relative_tangent_lift.py | cmp - EXACT-RELATIVE-TANGENT-LIFT.json
)
(
  cd actual-one-I-third-cover-minimization-r1
  python3 -B check_third_cover_minimization.py | cmp - EXACT-THIRD-COVER-MINIMIZATION.json
)
(
  cd actual-one-I-third-cover-reduced-r1
  python3 -B check_cfs_reduction.py | cmp - EXACT-REDUCTION-REPLAY.json
)
(
  cd actual-one-I-dual-plane-search-r1
  python3 -B check_dual_planes.py --jet 2 --bound 60000 | cmp - EXACT-59-DEEP2-SECOND-JET.json
)
(
  cd actual-one-I-seven-jet-quadrics-r1
  python3 -B check_seven_jet_quadrics.py | cmp - EXACT-COMPLETE-59-DEPTH1.json
  python3 -B check_seven_jet_quadrics.py --k 2 --partial 128 --force-first-exact 4 | cmp - EXACT-PILOT-59-DEPTH2-128.json
  python3 -B check_seven_jet_quadrics.py --k 2 --bound 500000 --workers 4 | cmp - EXACT-COMPLETE-59-DEPTH2.json
)
```

The last command took about 41 seconds on four workers. No network,
mathematical software beyond the stated Python dependency, or Lean
build is needed for these replays.
