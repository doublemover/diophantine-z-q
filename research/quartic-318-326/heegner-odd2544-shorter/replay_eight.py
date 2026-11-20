#!/usr/bin/env python3
"""Replay all independently checked weighted coefficient rows on the pinned q29 book."""
import argparse
import hashlib
import json
from math import gcd, isqrt
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
DEFAULT_BASE = (
    HERE.parent / "heegner-odd2544-theta" / "high-hom-1120"
    / "heegner-compressed-trace" / "odd2544-weight-primefree-r1"
)
PIN = {
    "ACTUAL-ODD2544-MARKED-ORDERS-Q29.json":
        "aa650e289ef886c824cf93414845c9586c12e5db0d640f6a6d48452ca9bb1a8e",
    "odd2544_reference_coefficients.py":
        "be160ba3f07261dda8f10aaec5f2196cef00b7d94e89fdc4c040cba2d06e660b",
}

def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def load(name):
    return json.loads((HERE / name).read_text())

def isprime(n):
    return n >= 2 and all(n % r for r in range(2, isqrt(n) + 1))

def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--baseline", type=Path, default=DEFAULT_BASE)
    p.add_argument("--cpp", type=Path, help="optional compiled rank3_exact_reps_small")
    opt = p.parse_args()
    base = opt.baseline.resolve()
    for name, expected in PIN.items():
        file = base / name
        if not file.is_file() or digest(file) != expected:
            p.error(f"missing/wrong exact dependency {file}")
    sys.path.insert(0, str(base))
    # The frozen lower-level driver captures argv[1] during import.
    # It does not use the supplied path in Python-only replay.
    sys.argv = [sys.argv[0], str(opt.cpp.resolve()) if opt.cpp else "/no-cpp-needed"]
    from recalibrate_short_auxiliaries import coeff, src, new_reps
    from check_negative_small import OLD_REPS

    assert src.SOURCE.resolve() == base / "ACTUAL-ODD2544-MARKED-ORDERS-Q29.json"
    book = json.loads(src.SOURCE.read_text())
    emit = new_reps if opt.cpp else OLD_REPS
    a = load("SHORT-AUXILIARIES-CALIBRATION.json")
    b = load("SHORT-MATCHED-LOCAL-COUNTERCONTROL.json")
    main_rows = [a[key] for key in (
        "first_positive_aux_seed", "first_negative_aux_seed",
        "reference_negative", "reference_positive",
    )]
    for row in b["rows"]:
        n, m = row["d"], row["m"]
        assert isprime(n) and m == 455 and gcd(n, m) == 1 and n % 24 == 11
        assert src.leg(-m, n) == 1 and src.leg(n, 53) == -1
        assert row["legendre"] == [src.leg(n, q) for q in b["legendre_places"]]
        assert row["negative"]["D"] == -n and row["positive"]["D"] == m*n
        main_rows.extend([row["negative"], row["positive"]])
    assert len(main_rows) == 8
    for value in main_rows:
        actual = json.loads(json.dumps(coeff(book, value["D"], value["aux_l"], emit)))
        assert actual == value, (value["D"], value["aux_l"], actual, value)
    k = a["ref_square"] * pow(
        (a["reference_negative"]["coefficient_mod13"]
         * a["reference_positive"]["coefficient_mod13"])**2, -1, 13
    ) % 13
    assert k == a["calibrated_multiplier_mod13"] == 10
    assert a["ref_square"] == a["ref_signed_13_projection"]**2 % 13
    assert b["rows"][0]["legendre"] == b["rows"][1]["legendre"]
    for row, expectation in zip(b["rows"], (0, 1)):
        value = k * (
            row["negative"]["coefficient_mod13"] * row["positive"]["coefficient_mod13"]
        )**2 % 13
        assert value == row["square_mod13"] == expectation

    (seed,) = load("FIXED-D323-POSITIVE-M1079-SEED.json")
    assert seed["D"] == 1079*323 and seed["coefficient_mod13"] == 4
    assert 1079 == 13*83 and 1079 % 24 == 23 and src.leg(1079, 53) == -1
    assert [src.leg(-1079, q) for q in (17, 19)] == [1, 1]
    assert [src.leg(seed["D"] // q, q) for q in (17, 19)] == [1, -1]
    assert json.loads(json.dumps(coeff(book, seed["D"], seed["aux_l"], emit))) == seed
    final_seed = coeff(book, 37, -35, emit)
    assert final_seed["raw_mod13_representatives_by_class"] == [-16, 120, 16, 56, -36]
    assert final_seed["coefficient_mod13"] == 10
    print("Verified 8 calibration/countercontrol rows and 2 supplementary seeds.")
    print("Same m=455 and matched symbols: residues squared 0 and 1.")

if __name__ == "__main__":
    main()
