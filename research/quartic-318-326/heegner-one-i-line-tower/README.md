# Exact degree-14 line tower for one actual historical base

This source-only packet gives a degree 14 → 6 → 2 presentation
of the point field of the actual order-13 point on
E_d for d=2811626664334219040035976315, and the exact discriminants
of its three fields. The explicit line generator is integral. Its
order is not asserted maximal. The relative tower and discriminants
are input for a possible faithful class-eigenspace calculation.
No class rank, scored global basis, Selmer dimension, rational
rank, rational point, or cyclotomic value is computed.

Start with [the proof](actual-one-I-explicit-line-field-r2/EXACT-LINE-TOWER-AND-DISCRIMINANTS.md)
and its [independent review](independent-review/INDEPENDENT-REVIEW.md).
The exact predecessor JSONs and replay sources are included
at the paths expected by the original scripts. The review
binds their reviewed main successor and its four machine files.

From this directory, with Python 3 and SymPy:

    sha256sum -c SHA256SUMS
    cd actual-one-I-cyclotomic13-r1
    python3 -B check_point_field13_presentation.py | cmp - EXACT-POINT-FIELD-13.json
    python3 -B check_local13_torsion.py | cmp - EXACT-LOCAL13-ORDINARY-WILD.json
    cd ../actual-one-I-explicit-line-field-r2
    python3 -B check_actual_line_field.py | cmp - ACTUAL-DEGREE14-LINE-FIELD.json
    python3 -B check_field_discriminants.py | cmp - ACTUAL-FIELD-DISCRIMINANTS.json

The first two replays verify the frozen degree-84 and mod-169
inputs. The third recovers the actual line/relative x equations
by exact modular CRT with proved trace bounds. The fourth checks
the discriminant, index, relative norm and digit arithmetic using
the proved local ramification analysis. The last replay is not a
general maximal-order package.

The [separately cold-checked parity note](actual-one-I-explicit-line-field-r2/PARITY-SAVES-ONE-LOCAL-RANK.md)
explains why a conditional local rank of 5+r₀ suffices, given a proved
faithful class bound r₀. No such bound or local rank is asserted here.
The independent signed tower receipt covers the tower and its four
replays, not this separate arithmetic implication.
