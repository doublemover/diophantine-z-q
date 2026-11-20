# Calibrated level-2544 residue test at the fixed field Q(sqrt(−455))

The exact five maximal and 416 marked Eichler orders support both
of the original fixed weight constructions. At the reference
d=323, the reductions of the two theta coefficients are 3 and
the conjugate pair 2,11 modulo 13. In the stated compatible
family *over this same field*, the exact squared trace residue
has calibration factor 10. Neither the new production coefficient
nor a new linked pole was evaluated. The different-field formula
appears only as a separate conditional normalization note.

Read [the fixed-field proof and coefficient definitions](high-hom-1120/heegner-compressed-trace/odd2544-weight-primefree-r1/EXACT-ODD2544-REFERENCE-COEFFICIENTS.md),
[the independent coefficient review](independent-review/INDEPENDENT-ODD2544-REFERENCE-REVIEW.md)
and [the original exact reference](../heegner-f53-fixed-example/README.md).
The independently reviewed math prose is reproduced with the fixed
field explicit and determinant-one frame choices written out.
The high-hom-1120 and joined-work-20261120 subdirectories are literal
source import paths inside this directory, not external directories.

Reproduce from this directory (Python 3.10+ and SymPy for the
integer Hermite normal forms; the weight and reference checks are
standard library only):

    export PYTHONDONTWRITEBYTECODE=1
    d=high-hom-1120/heegner-compressed-trace/odd2544-weight-primefree-r1
    python "$d/actual_odd2544_marked_orders_q29.py" > /tmp/q29-orders.json
    cmp /tmp/q29-orders.json "$d/ACTUAL-ODD2544-MARKED-ORDERS-Q29.json"
    python "$d/odd2544_reference_coefficients.py" > /tmp/ref2544.json
    cmp /tmp/ref2544.json "$d/ODD2544-REFERENCE-COEFFICIENTS.json"
    python "$d/check_odd2544_reference_reduction.py"
    sha256sum -c SHA256SUMS

The older fixed-level faster-norm analysis predates the explicit
marked-order and reference evaluator here; its proposed finite
objects are supplied by the new files, not by changing its text.

The four genuine degree-29 isogenies are prime to every fixed
weight place, and every supplied label is the actual geometric
level-48 mark. The arithmetic is exact. It is not an independently
specified characteristic-zero Hecke eigenvector or a completed
proof of the original quartic cases.
