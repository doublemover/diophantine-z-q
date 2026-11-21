# The ordinary mirror class certificate for one actual 13-Selmer problem

This is a source-only reduction on the historical base
d=2811626664334219040035976315. It does not certify a class
dimension, Selmer dimension, rational rank, or point.

- [Strict Selmer versus the ordinary class quotient](actual-one-I-strict-ordinary-class-r1/EXACT-STRICT-SELMER-ORDINARY-CLASS-CERTIFICATE.md):
  an independently certified projected ordinary class quotient
  of dimension at most one would suffice. This does not require
  computing a full Kummer basis or a ray class group.
- [Exact mirror pairing and prime 53](actual-one-I-mirror-ray-class-r1/EXACT-MIRROR-RAY-CLASS-UPPER-BOUND-CERTIFICATE.md):
  the intermediate construction explains the reflection character,
  its local modulus, and the actual matching degree-13 mirror prime.

The algebraic implications are unconditional; the factor-base
ceiling labelled GRH is only a practical comparison. The precise
actual q₅₃ residue address is computed. No principal reduction
of that ideal into a small factor base is claimed here.

Run from this directory with Python 3 and SymPy:

    set -eu
    set -o pipefail
    sha256sum -c SHA256SUMS
    (cd actual-one-I-cyclotomic13-r1 && python3 -B check_point_field13_presentation.py | cmp - EXACT-POINT-FIELD-13.json)
    (cd actual-one-I-cyclotomic13-r1 && python3 -B check_local13_torsion.py | cmp - EXACT-LOCAL13-ORDINARY-WILD.json)
    (cd actual-one-I-explicit-line-field-r2 && python3 -B check_actual_line_field.py | cmp - ACTUAL-DEGREE14-LINE-FIELD.json)
    (cd actual-one-I-explicit-line-field-r2 && python3 -B check_field_discriminants.py | cmp - ACTUAL-FIELD-DISCRIMINANTS.json)
    (cd actual-one-I-incidence-selmer-r1 && python3 -B check_point_covector_incidence.py | cmp - EXACT-POINT-COVECTOR-INCIDENCE.json)
    (cd actual-one-I-incidence-selmer-r1 && python3 -B check_actual_transvection_53.py | cmp - EXACT-ACTUAL-TRANSVECTION-53.json)
    (cd actual-one-I-mirror-ray-class-r1 && python3 -B check_actual_mirror_53.py | cmp - EXACT-ACTUAL-MIRROR-53-PRIME.json)
    (cd actual-one-I-strict-ordinary-class-r1 && python3 -B check_ordinary_factor_base_gap.py | cmp - EXACT-ORDINARY-FACTOR-BASE-GAP.json)

The [signed independent review](independent-review/INDEPENDENT-REVIEW.md)
covers the mirror and strict-class arguments, and independently
replays the exact degree-13 q₅₃ residue with separate arithmetic.
From this directory:

    (cd independent-review && sha256sum -c SHA256SUMS)
    python3 -B independent-review/check_mirror53_independent.py \
      actual-one-I-cyclotomic13-r1/EXACT-POINT-FIELD-13.json \
      actual-one-I-incidence-selmer-r1/EXACT-ACTUAL-TRANSVECTION-53.json \
      actual-one-I-mirror-ray-class-r1/EXACT-ACTUAL-MIRROR-53-PRIME.json \
      actual-one-I-explicit-line-field-r2/ACTUAL-FIELD-DISCRIMINANTS.json \
      | cmp - independent-review/EXACT-INDEPENDENT-53-REPLAY.txt
