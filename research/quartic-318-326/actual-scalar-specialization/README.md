# An exact original a=0 scalar specialization

The original 318/326 scalar construction can be instantiated at
the explicit index **h = 473592745039516333133760**. This
directory records its exact multiplier J, literal labels, local
scalar preparation and original guard and norm-margin tests.
It gives a compact specification of the very large exact rational
b. It does not use W=1 as a replacement for the computed W.

This is one scalar result. It does not supply the other three
coefficients at the same index, a marked rational point for this
b, the full squarefree part θ of 1−b/17, or either final theorem.
The two modular valuation-one results certify 131·6551|θ, not
that θ is their product. The proof note distinguishes the exact
expanded-height estimate of the ingredients from the unknown
degree of cancellation in the final rational.

## Replay

Python 3.10+, standard library only. From this directory:

    sha256sum -c SHA256SUMS
    PYTHONDONTWRITEBYTECODE=1 python3 select_scalar_specialization.py | cmp - EXACT-SCALAR-SPECIALIZATION.json
    PYTHONDONTWRITEBYTECODE=1 python3 check_actual_scalar_modular.py | cmp - ACTUAL-THETA-MODULAR-ROWS.json

The first script uses exact finite-field point arithmetic and
directed rounding with integer dyadic intervals, not floating
point. The second reduces the same literal b circuit modulo a
split prime square with exact, tracked p-adic precision. Neither
script expands the Lucas labels or the large rational, factors a
surrogate instead, or invokes Lean. The two accompanying notes
state the mathematical inputs and explain the reduction from
these reproducible checks to the claims.

The independent check recomputes all fifteen residue orders by
first return, not by the construction script's baby-step/giant-step
search. It also replays the prime-square data with weighted Jacobian
coordinates rather than affine p-adic balls:

    PYTHONDONTWRITEBYTECODE=1 python3 check_materialized_scalar.py

See [the independent review](INDEPENDENT-MATERIALIZED-SCALAR-REVIEW.md)
for the exact scope and acceptance decision.
