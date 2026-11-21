# One factor-free principal relation for the actual 13-point field

This packet concerns the historical one-I base
d=2811626664334219040035976315 only. It recovers a principal
ideal relation in the faithful mod-13 character of the
cyclic relative 13-point field, without factoring the
2379-digit residual norm cofactor. The cofactor and its
residue coordinates are preserved as the original integers,
not replaced with guessed prime support.

- [Principal norm and Tate coefficient](actual-one-I-principal-relation-r1/EXACT-FIRST-PROJECTED-PRINCIPAL-COEFFICIENT.md)
- [Factor-free composite support and the completed relation](actual-one-I-principal-composite-r1/EXACT-FACTOR-FREE-PRINCIPAL-IDEAL-RELATION.md)
- [Independent review](independent-review/INDEPENDENT-REVIEW.md)

The result is one exact relation
2eλ[q₃]+eλ[q₅₈₈₁]+eλ[I_C]=0 in (Cl(F)/13)_λ.
It neither certifies generators nor bounds the faithful
class rank. No Selmer dimension, rational rank, or point
is computed. The two exact earlier polynomial replays are
included; the earlier full local and field-discriminant
packets are separate research steps.

Run from this directory with Python 3 and SymPy:

    set -eu
    set -o pipefail
    sha256sum -c SHA256SUMS
    for d in actual-one-I-principal-relation-r1 actual-one-I-principal-composite-r1 independent-review; do
      (cd "$d" && sha256sum -c SHA256SUMS)
    done
    (cd actual-one-I-cyclotomic13-r1 && python3 -B check_point_field13_presentation.py | cmp - EXACT-POINT-FIELD-13.json)
    (cd actual-one-I-explicit-line-field-r2 && python3 -B check_actual_line_field.py | cmp - ACTUAL-DEGREE14-LINE-FIELD.json)
    (cd actual-one-I-principal-relation-r1 && python3 -B check_exact_first_principal.py | cmp - EXACT-FIRST-PRINCIPAL-DIVISOR.json)
    (cd actual-one-I-principal-composite-r1 && python3 -B check_composite_principal_support.py | cmp - EXACT-COMPOSITE-SUPPORT.json)
    python3 -B independent-review/check_relative_norm_and_composite.py \
      actual-one-I-explicit-line-field-r2/ACTUAL-DEGREE14-LINE-FIELD.json \
      actual-one-I-principal-relation-r1/EXACT-FIRST-PRINCIPAL-DIVISOR.json \
      actual-one-I-principal-composite-r1/EXACT-COMPOSITE-SUPPORT.json \
      actual-one-I-cyclotomic13-r1/EXACT-POINT-FIELD-13.json \
      | cmp - independent-review/EXACT-INDEPENDENT-REPLAY.txt

The full norm CRT is the longest author command (roughly
two minutes in the recorded run); the composite gcd takes
seconds. No external number-field database is used by the
replay. The independent code recomputes the signed norm by
multiplication determinants through the sextic/degree-14
tower, rather than reusing the author's degree-84 resultant.

## Deliberately shared residual: exact cancellation

The [second principal element](actual-one-I-deliberate-shared-support-r1/EXACT-DELIBERATE-SHARED-RESIDUAL.md)
was chosen to preserve the entire composite support. For
a=W−169B and R=1+(W+169B)/(3·5881), the proof verifies
that R is a unit at **every** prime above the original
cofactor C. The distinct principal element b=aR retains
the exact residual multiplicities of a. On the two known
labelled primes the faithful coefficients of R are −2,−1,
so those of b are zero. These are two independent
projected principal **divisors**; the ratio removes I_C
from their difference. Completeness, smoothness of the
remaining support of R, and a faithful class-rank bound
are not claimed.

Author replay, from the same directory:

    (cd actual-one-I-deliberate-shared-support-r1 && sha256sum -c SHA256SUMS)
    (cd actual-one-I-deliberate-shared-support-r1 && python3 -B check_deliberate_shared_support.py | cmp - EXACT-DELIBERATE-SHARED-SUPPORT.json)

See the [second independent review](independent-review-shared-residual/INDEPENDENT-REVIEW.md).
Its independent multiplication-determinant check applies directly
to the full composite modulus, not just the designated linear root.
From the same directory:

    (cd independent-review-shared-residual && sha256sum -c SHA256SUMS)
    python3 -B independent-review-shared-residual/check_shift_norm_unit.py \
      actual-one-I-explicit-line-field-r2/ACTUAL-DEGREE14-LINE-FIELD.json \
      actual-one-I-principal-relation-r1/EXACT-FIRST-PRINCIPAL-DIVISOR.json \
      actual-one-I-deliberate-shared-support-r1/EXACT-DELIBERATE-SHARED-SUPPORT.json \
      actual-one-I-cyclotomic13-r1/EXACT-POINT-FIELD-13.json \
      | cmp - independent-review-shared-residual/EXACT-INDEPENDENT-REPLAY.txt
