# Shorter fixed level-2544 theta coefficient replay

This folder records two shorter auxiliary weights on the same marked supersingular source and mod-13 period as the [original fixed example](../heegner-odd2544-theta/) and [varying-compatible-field extension](../heegner-odd2544-varying-cm/). The negative and positive ternary norm magnitudes fall by factors about 3972 and 9.23. The calibrated multiplier really is still 10.

The eight independently checked rows are two seed-chain rows, two reference rows, and the positive and negative rows for each of the two matched local controls. Both controls have the same required local signs at all the listed places. Their squared raw Heegner residues are 0 and 1. In the second, a nonzero rational Heegner point follows without replaying every orbit term. The fixed-d theorem proves infinitely many compatible auxiliary fields **after one actual unit seed**; the included seed holds d=323 fixed. It does not assert simultaneous nonvanishing for two twists at one field, realize any production index, give a point at the fixed large scalar, or verify Lean.

- [Arithmetic and calibration](SHORTER-ODD-AUXILIARIES-AND-LOCAL-COUNTERCONTROL.md)
- [The individually infinite local types](INFINITE-MOD13-UNITS-BUT-NOT-SELECTED-SUPPORT.md)
- [The fixed-d sieve and bounded nontorsion consequence](FIXED-D-FORCED-LOCAL-VALUATION-AND-POINTWISE-EXAMPLE.md)
- [Signed independent review](INDEPENDENT-SHORT-ODD-AND-FIXED-D-REVIEW.md)

## Reproduce

From this folder in the repository, run:

```sh
sha256sum -c SHA256SUMS
python3 -B replay_eight.py
```

Only standard-library Python and two exact files from the sibling original replay are required. The script checks their full SHA-256 digests before import. For a non-sibling checkout, pass `--baseline` pointing to the directory containing `ACTUAL-ODD2544-MARKED-ORDERS-Q29.json` and `odd2544_reference_coefficients.py`. The two supplementary seeds are also replayed.

Optional bounded C++ acceleration:

```sh
g++ -O3 -std=c++20 rank3_exact_reps_small.cpp -o /tmp/rank3_exact_reps_small
python3 -B replay_eight.py --cpp /tmp/rank3_exact_reps_small
```

The C++ path changes only the finite lattice-representation enumeration, not the source orders, weights, or orbit labels. The saved timing sample in `BOUNDED-ENUMERATOR-BENCHMARK.json` is historical, not a validation threshold. A separate same-enumerator benchmark is available with `check_negative_small.py` and `PYTHONPATH` set to the same baseline directory.
