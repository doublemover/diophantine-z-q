# Exact transvection tests for one actual 13-point field

This source-only packet concerns the historical one-I base
d=2811626664334219040035976315. The
[exact image theorem](actual-one-I-incidence-selmer-r1/EXACT-TRANSVECTION-IMAGE-TEST-FOR-ACTUAL-SEL13.md)
identifies which elements of an ambient faithful Kummer
space come from the global Weil-module cohomology:
the local residue score must vanish at every good prime
with nonidentity unipotent Frobenius. Once that global
descent is known, only the formal local condition at 13
remains for this curve's Selmer test.

At the actual good prime 53, the exact 13-degree residue
calculation detects the mixed ambient class eλ(2+W) with
score 8 in the designated orientation. It also checks
zero score for the sign-even control. The mixed element
is not asserted to be an admissible global S-class.
No numerical prime cutoff, class-group dimension,
global Selmer bound, rational rank, or point is computed.

Replay from this directory with Python 3 and SymPy:

    set -eu
    set -o pipefail
    sha256sum -c SHA256SUMS
    (cd actual-one-I-cyclotomic13-r1 && python3 -B check_point_field13_presentation.py | cmp - EXACT-POINT-FIELD-13.json)
    (cd actual-one-I-cyclotomic13-r1 && python3 -B check_local13_torsion.py | cmp - EXACT-LOCAL13-ORDINARY-WILD.json)
    (cd actual-one-I-incidence-selmer-r1 && sha256sum -c SHA256SUMS)
    (cd actual-one-I-incidence-selmer-r1 && python3 -B check_point_covector_incidence.py | cmp - EXACT-POINT-COVECTOR-INCIDENCE.json)
    (cd actual-one-I-incidence-selmer-r1 && python3 -B check_actual_transvection_53.py | cmp - EXACT-ACTUAL-TRANSVECTION-53.json)

The two predecessor kernels replay the literal degree-84
division polynomial and the 13-local mod-169 data. The
two new replays are finite incidence/coinvariant arithmetic
and a residue-field witness. Chebotarev supplies existence
in the proof, not a numerical finite cutoff here.

## Exact existence and density for a finite candidate space

The [joint density proof](actual-one-I-transvection-density-r1/EXACT-JOINT-TRANSVECTION-DENSITY.md)
uses the finite affine Galois extension of a given finite candidate
space. It shows that every projective row direction occurs and that
m tests suffice in existence on a quotient of dimension m.
This does not guarantee a short prime range or numerical cutoff.

The [independent review](independent-review/INDEPENDENT-REVIEW.md)
covers both arguments. Its separate finite field and group-law
replay reproduces the literal 53 residue scores.

    (cd actual-one-I-transvection-density-r1 && sha256sum -c SHA256SUMS)
    (cd actual-one-I-transvection-density-r1 && python3 -B check_transvection_counts.py | cmp - EXACT-TRANSVECTION-COUNTS.json)
    (cd independent-review && sha256sum -c SHA256SUMS)
    python3 -B independent-review/check_hom_transvection53_independent.py \
      actual-one-I-cyclotomic13-r1/EXACT-POINT-FIELD-13.json \
      actual-one-I-incidence-selmer-r1/EXACT-ACTUAL-TRANSVECTION-53.json \
      | cmp - independent-review/EXACT-INDEPENDENT-53-REPLAY.txt
